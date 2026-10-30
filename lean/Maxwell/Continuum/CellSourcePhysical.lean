import Maxwell.Continuum.CellSelectedDual
import Maxwell.Continuum.SourceNumerator
import Maxwell.Continuum.CellSpatialRestriction

/-! The cell dual pairing equals the literal spatial source integral.
This fixes its factor of eight before summing physical cells. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand FiberNormalization CellBandFourier MeasureTheory EffectiveMass

attribute [local instance] Measure.Subtype.measureSpace

theorem restrictCell_value_ae (f : FieldL2) :
    (fun t => cellFieldValue (restrictCell f) t) =ᵐ[torusMeasure]
      fun t => fieldValue f (spatialEquiv t).val := by
  have hj (j : Fin 3) : restrictCell f j =ᵐ[torusMeasure]
      fun t => f j (spatialEquiv t).val := by
    have ha := spatialUnitary_ae (restrictField f) j
    have hb := spatialEquiv_measurePreserving.quasiMeasurePreserving.ae_eq_comp (restrictScalar_ae (f j))
    filter_upwards [ha, hb] with t ha hb
    exact ha.trans hb
  filter_upwards [ae_all_iff.mpr hj] with t ht
  apply PiLp.ext
  intro j
  exact ht j

theorem cellMean_integral (F : Space → ℂ) :
    (∫ t, F (spatialEquiv t).val ∂torusMeasure) =
      (1/8 : ℂ) * ∫ x in physicalCell, F x := by
  rw [spatialEquiv_measurePreserving.integral_comp spatialEquiv.measurableEmbedding
    (fun x : physicalCell => F x.val)]
  change (∫ x : physicalCell, F x.val ∂((1/8 : ENNReal) • volume.comap Subtype.val)) = _
  rw [integral_smul_measure]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  rw [integral_subtype_comap physicalCell_measurable F]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]

theorem cellSourceFunctional_restrict {q : Momentum} (f : FieldL2) :
    cellSourceFunctional q (restrictCell f) = (1/8 : ℂ) *
      ∫ x in physicalCell, bilinear (physicalSelectedWave (-q) x) (fieldValue f x) := by
  rw [cellSourceFunctional]
  have he : (∫ t, bilinear (physicalSelectedWave (-q) (spatialEquiv t).val)
      (cellFieldValue (restrictCell f) t) ∂torusMeasure) =
      ∫ t, bilinear (physicalSelectedWave (-q) (spatialEquiv t).val)
        (fieldValue f (spatialEquiv t).val) ∂torusMeasure := by
    apply integral_congr_ae
    filter_upwards [restrictCell_value_ae f] with t ht
    rw [ht]
  rw [he]
  exact cellMean_integral (fun x => bilinear (physicalSelectedWave (-q) x) (fieldValue f x))

theorem sourceIntegrand_wave (h : ℝ) (u : FieldL2) (q : Momentum) (x : Space) :
    sourceIntegrand h u q x = bilinear (physicalSelectedWave q x) (sourceValue h u x) := by
  rw [physicalSelectedWave, map_smul, smul_apply]
  rfl

#print axioms cellSourceFunctional_restrict

end Maxwell.Continuum.CellGauge
