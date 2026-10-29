import Maxwell.Continuum.EffectiveMassScalingPacket
import Maxwell.Continuum.CellBandFourierMomentum

/-! Every constructed band packet has an L¹ Fourier representative,
because the momentum cell has finite measure and the actual band vector
has a uniform ℓ¹ alias bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.BandWavePacket

open MeasureTheory FreeFiber Bloch FiberNormalization

theorem quasiCell_subset_closedBall : quasiCell ⊆ Metric.closedBall (0 : Space) (3 * Real.pi) := by
  intro q hq
  rw [Metric.mem_closedBall, dist_zero_right]
  have hs : ‖q‖^2 ≤ 3 * (Real.pi / 2)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      (∑ j : Fin 3, ‖q j‖^2) ≤ ∑ _j : Fin 3, (Real.pi / 2)^2 := by
        apply Finset.sum_le_sum
        intro j _
        have hj : ‖q j‖ ≤ Real.pi / 2 := by
          rw [Real.norm_eq_abs, abs_le]
          exact ⟨by simpa only [neg_div] using (hq j).1, (hq j).2.le⟩
        exact pow_le_pow_left₀ (norm_nonneg _) hj 2
      _ = _ := by simp
  nlinarith [norm_nonneg q, Real.pi_pos]

instance quasiMeasure_finite : IsFiniteMeasure quasiMeasure := by
  have hq : (volume : Measure Space) quasiCell < ⊤ :=
    (measure_mono quasiCell_subset_closedBall).trans_lt measure_closedBall_lt_top
  let : IsFiniteMeasure ((volume : Measure Space).restrict quasiCell) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hq⟩
  have : IsFiniteMeasure ((volume.comap (Subtype.val : QuasiCell → Space)).map Subtype.val) := by
    rw [map_comap_subtype_coe quasiCell_measurable]
    infer_instance
  have : IsFiniteMeasure (volume.comap (Subtype.val : QuasiCell → Space)) :=
    Measure.isFiniteMeasure_of_map measurable_subtype_coe.aemeasurable
  change IsFiniteMeasure (Real.toNNReal ((2 * Real.pi)^3)⁻¹ •
    (volume.comap (Subtype.val : QuasiCell → Space)))
  infer_instance

theorem sectionValue_fourier_l1 (q : QuasiCell) :
    Summable (fun ν => ‖sectionValue q ν‖) ∧ ∑' ν, ‖sectionValue q ν‖ ≤ 32 := by
  by_cases hq : q ∈ region
  · rw [sectionValue_eq hq]
    exact normalizedFiberVector_fourier_l1 hq
  · rw [sectionValue_zero hq]
    simp only [lp.coeFn_zero, Pi.zero_apply, norm_zero, summable_zero, tsum_zero]
    norm_num

theorem component_fourier_l1 (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) (j : Fin 3) :
    Summable (fun ν => ‖u ν j‖) ∧ ∑' ν, ‖u ν j‖ ≤ ∑' ν, ‖u ν‖ := by
  have hs := hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ν => PiLp.norm_apply_le (u ν) j)
  exact ⟨hs, hs.tsum_le_tsum (fun ν => PiLp.norm_apply_le (u ν) j) hu⟩

theorem fiberEmbedding_fourier_l1_ae (f : Amplitude) :
    ∀ᵐ q ∂quasiMeasure, Summable (fun ν => ‖fiberEmbedding f q ν‖) ∧
      ∑' ν, ‖fiberEmbedding f q ν‖ ≤ 32 * ‖f.val q‖ := by
  filter_upwards [fiberEmbedding_ae f] with q hq
  have hs := sectionValue_fourier_l1 q
  have he (ν : FreeFiber.Alias) : ‖fiberEmbedding f q ν‖ = ‖f.val q‖ * ‖sectionValue q ν‖ := by
    rw [hq, lp.coeFn_smul, Pi.smul_apply, norm_smul]
  simp only [he, tsum_mul_left]
  refine ⟨hs.1.mul_left _, ?_⟩
  simpa only [mul_comm (32 : ℝ)] using mul_le_mul_of_nonneg_left hs.2 (norm_nonneg (f.val q))

theorem embedding_unfiber_integrable (f : Amplitude) (j : Fin 3) :
    Integrable (unfiberValue (fiberEmbedding f) j) (quasiMeasure.prod Measure.count) := by
  have hm := unfiberValue_stronglyMeasurable (fiberEmbedding f) j
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  have hrow : ∀ᵐ q ∂quasiMeasure,
      Integrable (fun ν : FreeFiber.Alias => fiberEmbedding f q ν j) Measure.count ∧
        (∫ ν : FreeFiber.Alias, ‖fiberEmbedding f q ν j‖ ∂Measure.count) ≤ 32 * ‖f.val q‖ := by
    filter_upwards [fiberEmbedding_fourier_l1_ae f] with q hq
    have hc := component_fourier_l1 (fiberEmbedding f q) hq.1 j
    have hi : Integrable (fun ν : FreeFiber.Alias => fiberEmbedding f q ν j) Measure.count := by
      rw [integrable_count_iff]
      exact hc.1
    refine ⟨hi, ?_⟩
    rw [integral_countable hi.norm]
    simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    exact hc.2.trans hq.2
  refine ⟨hrow.mono (fun _ hq => hq.1), ?_⟩
  apply ((Lp.memLp f.val).integrable (by norm_num)).norm.const_mul (32 : ℝ) |>.mono'
    hm.norm.integral_prod_right'.aestronglyMeasurable
  filter_upwards [hrow] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact hq.2

theorem physicalEmbedding_fourier_integrable (f : Amplitude) (j : Fin 3) :
    Integrable (fun ξ => fieldFourier (physicalEmbedding f) j ξ) := by
  apply (quasiFrequencyJoin_measurePreserving.integrable_comp_emb
    quasiFrequencyJoin.measurableEmbedding).mp
  apply (embedding_unfiber_integrable f j).congr
  have hc := unitary_coordinate_ae (physicalEmbedding f)
  rw [unitary_physicalEmbedding] at hc
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := quasiMeasure) (ν := (Measure.count : Measure FreeFiber.Alias))).ae hc
  filter_upwards [hp] with qν hqν
  exact hqν qν.2 j

#print axioms embedding_unfiber_integrable
#print axioms physicalEmbedding_fourier_integrable

end Maxwell.Continuum.BandWavePacket
