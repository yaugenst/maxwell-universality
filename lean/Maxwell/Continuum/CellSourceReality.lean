import Maxwell.Continuum.CellSourceAssembly
import Maxwell.Continuum.CellLatticePhase

/-! Real-source duality for the literal cell packet. The antiperiodic
carrier on the physical lattice is proved real, so no phase is dropped. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand FiberNormalization CellBandFourier MeasureTheory EffectiveMass Bloch

theorem carrier_twice_lattice (a : Bloch.Alias) :
    carrier (latticeShift a + latticeShift a) = 1 := by
  unfold carrier
  convert Complex.exp_int_mul_two_pi_mul_I (∑ j : Fin 3, a j) using 1
  congr 1
  simp only [latticeShift, PiLp.add_apply, PiLp.smul_apply,
    integerVector_apply, smul_eq_mul, Fin.sum_univ_three, Int.cast_add,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast,
    Complex.ofReal_div]
  ring

theorem carrier_neg_lattice (a : Bloch.Alias) :
    carrier (-latticeShift a) = carrier (latticeShift a) := by
  have he := carrier_add (-latticeShift a) (latticeShift a+latticeShift a)
  rw [carrier_twice_lattice, mul_one] at he
  simpa only [neg_add_cancel_left] using he.symm

theorem carrier_lattice_star (a : Bloch.Alias) :
    star (carrier (latticeShift a)) = carrier (latticeShift a) := by
  rw [star_carrier, carrier_neg_lattice]

theorem sourceLatticeFactor_star (q : Momentum) (a : Bloch.Alias) :
    star (sourceLatticeFactor (-star q) a) = sourceLatticeFactor q a := by
  rw [sourceLatticeFactor, star_mul', spatialPhase_star, carrier_lattice_star]
  simp only [star_neg, star_star, neg_neg, sourceLatticeFactor]

theorem fieldValue_real {f : FieldL2} (hf : fieldConjugation f = f) :
    ∀ᵐ x ∂volume, star (fieldValue f x) = fieldValue f x := by
  filter_upwards [ae_all_iff.mpr (fun j => scalarConjugation_ae (f j))] with x hx
  apply PiLp.ext
  intro j
  have he : scalarConjugation (f j) = f j := congrArg (fun v : FieldL2 => v j) hf
  have hj := hx j
  rw [he] at hj
  exact hj.symm

theorem restrictCell_real {f : FieldL2} (hf : fieldConjugation f = f) :
    ∀ᵐ t ∂torusMeasure, star (cellFieldValue (restrictCell f) t) =
      cellFieldValue (restrictCell f) t := by
  have hr := spatialEquiv_measurePreserving.quasiMeasurePreserving.ae
    (cell_mean_coe_measurePreserving.quasiMeasurePreserving.ae
      (Measure.ae_smul_measure (ae_restrict_of_ae (fieldValue_real hf)) (1/8 : ENNReal)))
  filter_upwards [restrictCell_value_ae f, hr] with t ht hr
  rw [ht]
  exact hr

theorem polarization_bilinear_comm (f g : Polarization) : bilinear f g = bilinear g f := by
  simp only [bilinear_apply, PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro j _
  change g j*star (star (f j)) = f j*star (star (g j))
  rw [star_star, star_star, mul_comm]

theorem selectedCellWave_pairing_real {q : Momentum} (hq : q ∈ physicalChart)
    {f : CellFieldL2} (hf : ∀ᵐ t ∂torusMeasure, star (cellFieldValue f t) = cellFieldValue f t) :
    inner ℂ f (selectedCellWave q) = cellSourceFunctional (-q) f := by
  rw [cell_inner_integral, cellSourceFunctional, neg_neg]
  apply integral_congr_ae
  filter_upwards [hf, ae_all_iff.mpr (fun j : Fin 3 => selectedCellWave_ae hq j)] with t ht hw
  have he : cellFieldValue (selectedCellWave q) t = physicalSelectedWave q (spatialEquiv t).val := by
    apply PiLp.ext
    intro j
    exact hw j
  rw [he, polarization_bilinear_comm, bilinear_apply, ht]

theorem cellSourcePacket_wave_pairing {h : ℝ} {u : FieldL2} (hu : fieldConjugation u = u)
    {q : Momentum} (hq : q ∈ physicalChart) :
    inner ℂ (cellSourcePacket h u (star q)) (selectedCellWave q) =
      cellSourceFunctional (-q) (cellSourcePacket h u (-q)) := by
  rw [cellSourceFunctional_packet (source_physicalChart_neg hq), cellSourcePacket, sum_inner]
  apply Finset.sum_congr rfl
  intro a _
  rw [inner_smul_left, starRingEnd_apply, sourceLatticeFactor_star, neg_neg]
  congr 1
  exact selectedCellWave_pairing_real hq (restrictCell_real
    (fieldTranslation_preserves_real (latticeShift a) (sourceMode_real h hu)))

#print axioms cellSourcePacket_wave_pairing

end Maxwell.Continuum.CellGauge
