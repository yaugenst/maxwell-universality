import Maxwell.Continuum.EffectiveMassConstantPacket
import Maxwell.Continuum.EffectiveMassPacketIntegral

/-! Exact inverse-Fourier reconstruction of the fixed zero-momentum
Bloch section. Every alias of the normalized reference fiber is retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FourierTransform FreeFiber Bloch BandWavePacket PeriodicBand CellBandFourier

attribute [local irreducible] physicalFiberVector

theorem constantFiber_fourier_l1 :
    Summable (fun ν => ‖physicalFiberVector 0 ν‖) ∧ ∑' ν, ‖physicalFiberVector 0 ν‖ ≤ 32 := by
  simpa only [physicalFiberVector, unscale, smul_zero] using
    FiberNormalization.normalizedFiberVector_fourier_l1 chart_zero

theorem constant_unfiber_integrable (f : Amplitude) (j : Fin 3) :
    Integrable (unfiberValue (constantSection.embedding f) j) (quasiMeasure.prod Measure.count) := by
  have hm := unfiberValue_stronglyMeasurable (constantSection.embedding f) j
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  have hc := component_fourier_l1 (physicalFiberVector 0) constantFiber_fourier_l1.1 j
  have hrow : ∀ᵐ q ∂quasiMeasure,
      Integrable (fun ν : FreeFiber.Alias => constantSection.embedding f q ν j) Measure.count ∧
        (∫ ν : FreeFiber.Alias, ‖constantSection.embedding f q ν j‖ ∂Measure.count) ≤ 32 * ‖f.val q‖ := by
    filter_upwards [constantFiber_ae f] with q hq
    have he (ν : FreeFiber.Alias) : ‖constantSection.embedding f q ν j‖ =
        ‖f.val q‖ * ‖physicalFiberVector 0 ν j‖ := by
      rw [hq, lp.coeFn_smul, Pi.smul_apply, PiLp.smul_apply, norm_smul]
    have hi : Integrable (fun ν : FreeFiber.Alias => constantSection.embedding f q ν j) Measure.count := by
      rw [integrable_count_iff]
      simp_rw [he]
      exact hc.1.mul_left _
    refine ⟨hi, ?_⟩
    rw [integral_countable hi.norm]
    simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul, he, tsum_mul_left]
    have hb := mul_le_mul_of_nonneg_left (hc.2.trans constantFiber_fourier_l1.2) (norm_nonneg (f.val q))
    simpa only [mul_comm (32 : ℝ)] using hb
  refine ⟨hrow.mono (fun _ hq => hq.1), ?_⟩
  apply ((Lp.memLp f.val).integrable (by norm_num)).norm.const_mul (32 : ℝ) |>.mono'
    hm.norm.integral_prod_right'.aestronglyMeasurable
  filter_upwards [hrow] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact hq.2

theorem constantPhysicalEmbedding_fourier_integrable (f : Amplitude) (j : Fin 3) :
    Integrable (fun ξ => fieldFourier (constantPhysicalEmbedding f) j ξ) := by
  apply (quasiFrequencyJoin_measurePreserving.integrable_comp_emb
    quasiFrequencyJoin.measurableEmbedding).mp
  apply (constant_unfiber_integrable f j).congr
  have hc := unitary_coordinate_ae (constantPhysicalEmbedding f)
  rw [constantPhysicalEmbedding_unitary] at hc
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := quasiMeasure) (ν := (Measure.count : Measure FreeFiber.Alias))).ae hc
  filter_upwards [hp] with qν hqν
  exact hqν qν.2 j

theorem constantPhysicalEmbedding_integral (f : Amplitude) (j : Fin 3) :
    constantPhysicalEmbedding f j =ᵐ[volume] fun x => ∫ q : QuasiCell,
      f.val q * (blochField (physicalMomentum q.val) (physicalFiberVector 0) x) j ∂quasiMeasure := by
  have hinv := fourierInvL2_ae_integral (fieldFourier (constantPhysicalEmbedding f) j)
    (constantPhysicalEmbedding_fourier_integrable f j)
  change (𝓕⁻ (𝓕 (constantPhysicalEmbedding f j)) : ScalarL2) =ᵐ[volume] _ at hinv
  rw [fourierInv_fourier_eq] at hinv
  filter_upwards [hinv] with x hx
  rw [hx, inverseFourier_eq_angular]
  have hfreq := unitary_frequency_product_ae (constantPhysicalEmbedding f) j
  rw [constantPhysicalEmbedding_unitary] at hfreq
  have heq : (fun qν : QuasiCell × FreeFiber.Alias =>
      angularPhase ((2 * Real.pi) • quasiFrequencyJoin qν) x *
        fieldFourier (constantPhysicalEmbedding f) j (quasiFrequencyJoin qν)) =ᵐ[
      quasiMeasure.prod Measure.count]
      fun qν => angularPhase (aliasFrequency qν.1.val qν.2) x *
        constantSection.embedding f qν.1 qν.2 j := by
    filter_upwards [hfreq] with qν hqν
    rw [quasiFrequencyJoin_aliasFrequency, hqν]
    rfl
  have hi := quasiFrequencyJoin_measurePreserving.integrable_comp_of_integrable
    (inversePhase_integrable (fieldFourier (constantPhysicalEmbedding f) j)
      (constantPhysicalEmbedding_fourier_integrable f j) x)
  have hi' : Integrable (fun qν : QuasiCell × FreeFiber.Alias =>
      angularPhase (aliasFrequency qν.1.val qν.2) x * constantSection.embedding f qν.1 qν.2 j)
      (quasiMeasure.prod Measure.count) := hi.congr heq
  rw [← quasiFrequencyJoin_measurePreserving.integral_comp'
    (fun ξ => angularPhase ((2 * Real.pi) • ξ) x * fieldFourier (constantPhysicalEmbedding f) j ξ),
    integral_congr_ae heq, integral_prod _ hi']
  apply integral_congr_ae
  filter_upwards [constantFiber_ae f, hi'.prod_right_ae] with q hq hrow
  rw [integral_countable hrow]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  have hs := (PiLp.proj 2 (fun _ : Fin 3 => ℂ) j : Polarization →L[ℂ] ℂ).hasSum
    (aliasWave_hasSum q.val (physicalFiberVector 0) constantFiber_fourier_l1.1 x)
  have hterm (ν : FreeFiber.Alias) :
      angularPhase (aliasFrequency q.val ν) x * constantSection.embedding f q ν j =
        f.val q * (aliasWave q.val (physicalFiberVector 0) x ν) j := by
    rw [hq, lp.coeFn_smul, Pi.smul_apply, PiLp.smul_apply]
    change angularPhase (aliasFrequency q.val ν) x * (f.val q * physicalFiberVector 0 ν j) =
      f.val q * (angularPhase (aliasFrequency q.val ν) x * physicalFiberVector 0 ν j)
    ring
  simp only [hterm, tsum_mul_left]
  congr 1
  exact hs.tsum_eq

#print axioms constantPhysicalEmbedding_integral

end Maxwell.Continuum.EffectiveMass
