import Maxwell.Continuum.EffectiveMassConstantIntegral
import Maxwell.Continuum.EffectiveMassPacketMask
import Maxwell.Continuum.EffectiveMassEnvelope
import Maxwell.Continuum.EffectiveMassAngularInverse

/-! The fixed-fiber Bloch packet is exactly the normalized spatial
envelope, after the literal scalar momentum-chart projection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber Bloch BandWavePacket PeriodicBand CellBandFourier

attribute [local irreducible] physicalFiberVector constantPhysicalEmbedding

theorem packetRegion_finite {h : ℝ} (hh : 0 < h) : volume (packetRegion h) ≠ ⊤ := by
  have hs : packetRegion h ⊆ Metric.closedBall (0 : Space) (3 * Real.pi / h) := by
    intro p hp
    have hq := quasiCell_subset_closedBall hp.1
    rw [Metric.mem_closedBall, dist_zero_right, scaled_norm hh.le] at hq
    rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hh]
    simpa only [mul_comm] using hq
  exact ((measure_mono hs).trans_lt measure_closedBall_lt_top).ne

theorem packetMask_integrable {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    Integrable (fun p => packetMask h f p) := by
  apply ((integrableOn_Lp_of_measure_ne_top f (by norm_num) (packetRegion_finite hh)).integrable_indicator
    (packetRegion_measurable h)).congr
  exact (packetMask_ae h f).symm

theorem scaledDensity_amplitudeFactor {h : ℝ} (hh : 0 < h) :
    scaledDensity h * amplitudeFactor h = L2Dilation.factor h⁻¹ * fourierNormalization := by
  have hd := Real.sq_sqrt (scaledDensity_pos hh).le
  have hn := (Real.sqrt_pos.mpr (scaledDensity_pos hh)).ne'
  have hc : 0 ≤ fourierNormalization := Real.rpow_nonneg (by positivity) _
  calc
    _ = Real.sqrt (scaledDensity h) := by
      rw [amplitudeFactor]
      calc
        _ = (Real.sqrt (scaledDensity h))^2 * (Real.sqrt (scaledDensity h))⁻¹ :=
          congrArg (fun t : ℝ => t * (Real.sqrt (scaledDensity h))⁻¹) hd.symm
        _ = _ := by rw [pow_two, mul_assoc, mul_inv_cancel₀ hn, mul_one]
    _ = fourierNormalization * Real.sqrt (h^3) := by
      rw [scaledDensity, ← fourierNormalization_square, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]
    _ = _ := by
      rw [L2Dilation.factor, inv_pow, Real.sqrt_inv, inv_inv]
      exact mul_comm _ _

theorem scaledAmplitude_phase_integral {h : ℝ} (hh : 0 < h) (f : ScalarL2) (x : Space) :
    (∫ q : QuasiCell, (scaledAmplitude hh f).val q * angularPhase q.val x ∂quasiMeasure) =
      (scaledDensity h * amplitudeFactor h : ℂ) *
        ∫ p, (packetRegion h).indicator f p * angularPhase p (h • x) := by
  have he : (fun q : QuasiCell => (scaledAmplitude hh f).val q * angularPhase q.val x) =ᵐ[quasiMeasure]
      region.indicator (fun q => (amplitudeFactor h : ℂ) * f (h⁻¹ • q.val) * angularPhase q.val x) := by
    filter_upwards [scaledAmplitude_ae hh f] with q hq
    rw [hq]
    by_cases hr : q ∈ region
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr, zero_mul]
  rw [integral_congr_ae he, quasi_scaled_chart_integral hh
    (fun q : Space => (amplitudeFactor h : ℂ) * f (h⁻¹ • q) * angularPhase q x),
    Complex.real_smul, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    dsimp only
    by_cases hp : p ∈ packetRegion h
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, smul_smul,
        inv_mul_cancel₀ hh.ne', one_smul, angularPhase_smul]
      ring
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
      ring

theorem constant_bloch_cell (q x : Space) (j : Fin 3) :
    Complex.I * blochField (physicalMomentum q) (physicalFiberVector 0) x j =
      angularPhase q x * cellEigenfunction 0 x j := by
  have hzero : physicalFiberVector 0 = FiberNormalization.normalizedFiberVector 0 := by
    simp only [physicalFiberVector, unscale, smul_zero]
  rw [blochField, spatialPhase_physical, hzero, cellEigenfunction]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

theorem constantUh_integral {h : ℝ} (hh : 0 < h) (f : ScalarL2) (j : Fin 3) :
    constantUh hh f j =ᵐ[volume] fun x =>
      (scaledDensity h * amplitudeFactor h : ℂ) *
        (∫ p, (packetRegion h).indicator f p * angularPhase p (h • x)) * cellEigenfunction 0 x j := by
  filter_upwards [constantPhysicalEmbedding_integral (scaledAmplitude hh f) j,
    Lp.coeFn_smul Complex.I (constantPhysicalEmbedding (scaledAmplitude hh f) j)] with x hi hs
  change (Complex.I • constantPhysicalEmbedding (scaledAmplitude hh f) j) x = _
  rw [hs, Pi.smul_apply, smul_eq_mul, hi]
  have hg : Complex.I * (∫ q : QuasiCell, (scaledAmplitude hh f).val q *
      blochField (physicalMomentum q.val) (physicalFiberVector 0) x j ∂quasiMeasure) =
      (∫ q : QuasiCell, (scaledAmplitude hh f).val q * angularPhase q.val x ∂quasiMeasure) *
        cellEigenfunction 0 x j := by
    rw [← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q => by
      dsimp only
      rw [mul_left_comm Complex.I, constant_bloch_cell]
      ring
  rw [hg, scaledAmplitude_phase_integral hh]

theorem constantUh_eq_envelope {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    constantUh hh f = envelopeOperator hh ((angularFourier ℂ).symm (packetMask h f)) := by
  have hinv := angularFourier_inverse_integral (packetMask h f) (packetMask_integrable hh f)
  have hscaled := L2Dilation.inverse_ae (inv_pos.mpr hh) hinv
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [constantUh_integral hh f j,
    envelopeOperator_ae hh ((angularFourier ℂ).symm (packetMask h f)) j, hscaled]
    with x hu he hx
  rw [hu, he]
  simp only [inv_inv] at hx
  rw [hx]
  have hi : (∫ p, angularPhase p (h • x) • packetMask h f p) =
      ∫ p, (packetRegion h).indicator f p * angularPhase p (h • x) := by
    apply integral_congr_ae
    filter_upwards [packetMask_ae h f] with p hp
    rw [hp, smul_eq_mul, mul_comm]
  have hfactor := congrArg (fun r : ℝ => (r : ℂ)) (scaledDensity_amplitudeFactor hh)
  simp only [Complex.ofReal_mul] at hfactor
  rw [hi, hfactor]
  simp only [smul_eq_mul, fourierNormalization]
  ring

theorem constantUh_operator_eq_envelope {h : ℝ} (hh : 0 < h) :
    constantUh hh = (envelopeOperator hh).comp
      ((angularFourier ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (packetMask h)) := by
  apply ContinuousLinearMap.ext
  exact constantUh_eq_envelope hh

#print axioms constantUh_eq_envelope
#print axioms constantUh_operator_eq_envelope

end Maxwell.Continuum.EffectiveMass
