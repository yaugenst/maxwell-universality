import Maxwell.Continuum.BlochFreeSymbol

/-! Exact maximal free curl-curl graph under the literal Bloch unitary. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory Set
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

def quasiMomentum (q : QuasiCell) : FreeFiber.Momentum := fun i => ((q : Space) i : ℂ)

theorem physicalMomentum_join (q : QuasiCell) (n : Alias) :
    physicalMomentum (quasiFrequencyJoin (q, n)) = FreeFiber.aliasMomentum (quasiMomentum q) n := by
  funext i
  simp only [physicalMomentum, quasiFrequencyJoin_apply, FreeFiber.aliasMomentum, quasiMomentum]
  push_cast
  field_simp
  ring

/-- This is the literal distributional curl-curl equation with an L² source. -/
def WeakFreeEquation (E : ℂ) (u v : FieldL2) : Prop :=
  curlDistribution (curlDistribution (fieldDistribution u)) - E • fieldDistribution u =
    fieldDistribution v

theorem weakFreeEquation_fourier_iff (E : ℂ) (u v : FieldL2) :
    WeakFreeEquation E u v ↔
      ∀ i : Fin 3, (fun ξ => FreeFiber.block (physicalMomentum ξ) E
        (pointPolarization (fieldFourier u) ξ) i) =ᵐ[volume] fieldFourier v i := by
  unfold WeakFreeEquation
  rw [← distributionFourier_injective.eq_iff]
  simp only [map_sub, map_smul, distributionFourier_curl, fieldDistribution_fourier, smul_smul]
  rw [← pow_two]
  exact frequencyCross_twice_eq_iff E (fieldFourier u) (fieldFourier v)

theorem pointBlock_measurable (E : ℂ) (u : FieldL2) (i : Fin 3) :
    Measurable (fun ξ => FreeFiber.block (physicalMomentum ξ) E (pointPolarization u ξ) i) := by
  have he : (fun ξ => FreeFiber.block (physicalMomentum ξ) E (pointPolarization u ξ) i) =
      rowValue (curlCurlCoefficients E i) (curlCurlInputs u i) :=
    funext fun ξ => (curlCurl_rowValue_eq_block E u ξ i).symm
  rw [he]
  apply Finset.measurable_fun_sum
  intro j _
  exact (curlCurlCoefficients_temperate E i j).1.continuous.measurable.mul
    (Lp.stronglyMeasurable (curlCurlInputs u i j)).measurable

theorem ae_join_iff {p : Space → Prop} (hp : MeasurableSet {ξ | p ξ}) :
    (∀ᵐ ξ ∂(volume : Measure Space), p ξ) ↔
      ∀ᵐ q ∂quasiMeasure, ∀ n : Alias, p (quasiFrequencyJoin (q, n)) := by
  rw [← quasiFrequencyJoin_measurePreserving.map_eq,
    ae_map_iff quasiFrequencyJoin.measurable.aemeasurable hp]
  have hm : MeasurableSet {qn : QuasiCell × Alias | p (quasiFrequencyJoin qn)} :=
    hp.preimage quasiFrequencyJoin.measurable
  rw [Measure.ae_prod_iff_ae_ae hm]
  simp only [Measure.ae_count_iff]

theorem unitary_pointPolarization_ae (u : FieldL2) :
    ∀ᵐ q ∂quasiMeasure, ∀ n : Alias,
      pointPolarization (fieldFourier u) (quasiFrequencyJoin (q, n)) = unitary u q n := by
  filter_upwards [unitary_coordinate_ae u] with q hq
  intro n
  apply PiLp.ext
  intro i
  exact (hq n i).symm

/-- The physical distributional graph is exactly the direct integral of the
already constructed maximal alias operator. This equivalence imposes no
separate L² condition on the longitudinal derivative terms. -/
theorem weakFreeEquation_iff_fiber_graph (E : ℂ) (u v : FieldL2) :
    WeakFreeEquation E u v ↔
      ∀ᵐ q ∂quasiMeasure,
        (unitary u q, unitary v q) ∈ (FreeFiber.operator (quasiMomentum q) E).graph := by
  rw [weakFreeEquation_fourier_iff]
  have hjoin (i : Fin 3) := ae_join_iff
    (measurableSet_eq_fun (pointBlock_measurable E (fieldFourier u) i)
      (Lp.stronglyMeasurable (fieldFourier v i)).measurable)
  constructor
  · intro h
    have hh := ae_all_iff.mpr (fun i : Fin 3 => (hjoin i).mp (h i))
    filter_upwards [hh, unitary_pointPolarization_ae u, unitary_coordinate_ae v] with q hq hu hv
    rw [FreeFiber.operator_graph_iff]
    intro n
    apply PiLp.ext
    intro i
    have hi := hq i n
    rw [physicalMomentum_join, hu n, ← hv n i] at hi
    exact hi
  · intro h i
    apply (hjoin i).mpr
    filter_upwards [h, unitary_pointPolarization_ae u, unitary_coordinate_ae v] with q hq hu hv
    rw [FreeFiber.operator_graph_iff] at hq
    intro n
    rw [physicalMomentum_join, hu n, hq n]
    exact hv n i

end Maxwell.Continuum.Bloch
