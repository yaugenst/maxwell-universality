import Maxwell.Continuum.CellSourcePhysical
import Maxwell.Continuum.CellSpatialCover

/-! Exact source pairings on every translated period cell. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand FiberNormalization CellBandFourier MeasureTheory EffectiveMass Bloch Set

theorem spatialPhase_space_add (q : Momentum) (x y : Space) :
    spatialPhase q (x+y) = spatialPhase q x * spatialPhase q y := by
  simp only [spatialPhase, PiLp.add_apply, Complex.ofReal_add, mul_add,
    Finset.sum_add_distrib, Complex.exp_add]

def sourceLatticeFactor (q : Momentum) (a : Bloch.Alias) : ℂ :=
  spatialPhase q (latticeShift a) * carrier (latticeShift a)

theorem physicalSelectedWave_add_lattice (q : Momentum) (x : Space) (a : Bloch.Alias) :
    physicalSelectedWave q (x+latticeShift a) =
      sourceLatticeFactor q a • physicalSelectedWave q x := by
  unfold physicalSelectedWave cellEigenfunction antiperiodicField
  have ht : periodicField (normalizedFiberVector (unscale q)) (x+latticeShift a) =
      periodicField (normalizedFiberVector (unscale q)) x := periodicField_period _ x a
  rw [spatialPhase_space_add, carrier_add, ht]
  simp only [smul_smul, sourceLatticeFactor]
  congr 1
  ring

theorem fieldValue_translation_ae (a : Space) (f : FieldL2) :
    (fun x => fieldValue (fieldTranslation a f) x) =ᵐ[volume]
      fun x => fieldValue f (x+a) := by
  filter_upwards [ae_all_iff.mpr (fun j : Fin 3 => fieldTranslation_ae a f j)] with x hx
  apply PiLp.ext
  intro j
  exact hx j

theorem setIntegral_spatialBox (a : Bloch.Alias) (F : Space → ℂ) :
    (∫ x in spatialBox a, F x) = ∫ x in physicalCell, F (x+latticeShift a) := by
  have he := (measurePreserving_add_right volume (latticeShift a)).setIntegral_preimage_emb
    (Homeomorph.addRight (latticeShift a)).measurableEmbedding F (spatialBox a)
  have hs : (fun x : Space => x+latticeShift a) ⁻¹' spatialBox a = physicalCell := by
    ext x
    simp only [mem_preimage, spatialBox, mem_ofPred_eq, add_sub_cancel_right]
  rw [hs] at he
  exact he.symm

theorem cellSourceFunctional_lattice (q : Momentum) (a : Bloch.Alias) (f : FieldL2) :
    (∫ x in spatialBox a, bilinear (physicalSelectedWave (-q) x) (fieldValue f x)) =
      (8 : ℂ) * sourceLatticeFactor (-q) a * cellSourceFunctional q (restrictLatticeCell a f) := by
  rw [setIntegral_spatialBox]
  simp_rw [physicalSelectedWave_add_lattice, map_smul, smul_apply, smul_eq_mul]
  rw [integral_const_mul]
  have ht : (∫ x in physicalCell, bilinear (physicalSelectedWave (-q) x)
      (fieldValue f (x+latticeShift a))) =
      ∫ x in physicalCell, bilinear (physicalSelectedWave (-q) x)
        (fieldValue (fieldTranslation (latticeShift a) f) x) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (fieldValue_translation_ae (latticeShift a) f)] with x hx
    rw [hx]
  rw [ht]
  change sourceLatticeFactor (-q) a * (∫ x in physicalCell,
    bilinear (physicalSelectedWave (-q) x) (fieldValue (fieldTranslation (latticeShift a) f) x)) =
      (8 : ℂ)*sourceLatticeFactor (-q) a*cellSourceFunctional q (restrictCell (fieldTranslation (latticeShift a) f))
  rw [cellSourceFunctional_restrict]
  ring

#print axioms cellSourceFunctional_lattice

end Maxwell.Continuum.CellGauge
