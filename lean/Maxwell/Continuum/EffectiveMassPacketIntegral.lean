import Maxwell.Continuum.EffectiveMassPacketL1
import Maxwell.Continuum.EffectiveMassFourierInverse
import Maxwell.Continuum.EffectiveMassKernelSeries

/-! Inverse Fourier reconstruction of the actual Bloch-band embedding.
The equality is proved in physical L², not assumed as a packet formula. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FourierTransform FreeFiber CellBandFourier Bloch BandWavePacket

theorem quasiFrequencyJoin_aliasFrequency (q : QuasiCell) (ν : FreeFiber.Alias) :
    (2 * Real.pi) • quasiFrequencyJoin (q, ν) = aliasFrequency q.val ν := by
  apply PiLp.ext
  intro j
  simp only [PiLp.smul_apply, quasiFrequencyJoin_apply, aliasFrequency,
    PiLp.add_apply, corner, integerVector_apply, smul_eq_mul]
  field_simp

theorem inversePhase_integrable (u : ScalarL2) (hu : Integrable (fun ξ => u ξ)) (x : Space) :
    Integrable (fun ξ => angularPhase ((2 * Real.pi) • ξ) x * u ξ) := by
  have hm : Continuous (fun ξ => angularPhase ((2 * Real.pi) • ξ) x) := by
    unfold angularPhase
    fun_prop
  apply hu.norm.mono' (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
  exact Filter.Eventually.of_forall fun ξ => by
    change ‖angularPhase ((2 * Real.pi) • ξ) x * u ξ‖ ≤ ‖u ξ‖
    rw [norm_mul, angularPhase_norm, one_mul]

theorem inverseFourier_eq_angular (u : Space → ℂ) (x : Space) :
    𝓕⁻ u x = ∫ ξ, angularPhase ((2 * Real.pi) • ξ) x * u ξ := by
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    simp only [angularPhase, real_inner_smul_left, smul_eq_mul]

theorem unitary_frequency_product_ae (u : FieldL2) (j : Fin 3) :
    (fun qν : QuasiCell × FreeFiber.Alias => fieldFourier u j (quasiFrequencyJoin qν)) =ᵐ[
      quasiMeasure.prod Measure.count] unfiberValue (unitary u) j := by
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := quasiMeasure) (ν := (Measure.count : Measure FreeFiber.Alias))).ae (unitary_coordinate_ae u)
  filter_upwards [hp] with qν hqν
  exact (hqν qν.2 j).symm

theorem physicalEmbedding_integral (f : Amplitude) (j : Fin 3) :
    physicalEmbedding f j =ᵐ[volume] fun x => ∫ q : QuasiCell,
      f.val q * (blochField (physicalMomentum q.val) (sectionValue q) x) j ∂quasiMeasure := by
  have hinv := fourierInvL2_ae_integral (fieldFourier (physicalEmbedding f) j)
    (physicalEmbedding_fourier_integrable f j)
  change (𝓕⁻ (𝓕 (physicalEmbedding f j)) : ScalarL2) =ᵐ[volume] _ at hinv
  rw [fourierInv_fourier_eq] at hinv
  filter_upwards [hinv] with x hx
  rw [hx, inverseFourier_eq_angular]
  have hfreq := unitary_frequency_product_ae (physicalEmbedding f) j
  rw [unitary_physicalEmbedding] at hfreq
  have heq : (fun qν : QuasiCell × FreeFiber.Alias =>
      angularPhase ((2 * Real.pi) • quasiFrequencyJoin qν) x *
        fieldFourier (physicalEmbedding f) j (quasiFrequencyJoin qν)) =ᵐ[
      quasiMeasure.prod Measure.count]
      fun qν => angularPhase (aliasFrequency qν.1.val qν.2) x * fiberEmbedding f qν.1 qν.2 j := by
    filter_upwards [hfreq] with qν hqν
    rw [quasiFrequencyJoin_aliasFrequency, hqν]
    rfl
  have hi := quasiFrequencyJoin_measurePreserving.integrable_comp_of_integrable
    (inversePhase_integrable (fieldFourier (physicalEmbedding f) j)
      (physicalEmbedding_fourier_integrable f j) x)
  have hi' : Integrable (fun qν : QuasiCell × FreeFiber.Alias =>
      angularPhase (aliasFrequency qν.1.val qν.2) x * fiberEmbedding f qν.1 qν.2 j)
      (quasiMeasure.prod Measure.count) := hi.congr heq
  rw [← quasiFrequencyJoin_measurePreserving.integral_comp'
    (fun ξ => angularPhase ((2 * Real.pi) • ξ) x * fieldFourier (physicalEmbedding f) j ξ),
    integral_congr_ae heq, integral_prod _ hi']
  apply integral_congr_ae
  filter_upwards [fiberEmbedding_ae f, hi'.prod_right_ae] with q hq hrow
  rw [integral_countable hrow]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  have hs := (PiLp.proj 2 (fun _ : Fin 3 => ℂ) j : Polarization →L[ℂ] ℂ).hasSum
    (aliasWave_hasSum q.val (sectionValue q) (sectionValue_fourier_l1 q).1 x)
  have hterm (ν : FreeFiber.Alias) :
      angularPhase (aliasFrequency q.val ν) x * fiberEmbedding f q ν j =
        f.val q * (aliasWave q.val (sectionValue q) x ν) j := by
    rw [hq, lp.coeFn_smul, Pi.smul_apply, PiLp.smul_apply]
    change angularPhase (aliasFrequency q.val ν) x * (f.val q * sectionValue q ν j) =
      f.val q * (angularPhase (aliasFrequency q.val ν) x * sectionValue q ν j)
    ring
  simp only [hterm, tsum_mul_left]
  congr 1
  exact hs.tsum_eq

#print axioms physicalEmbedding_integral

end Maxwell.Continuum.EffectiveMass
