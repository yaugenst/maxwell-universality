import Maxwell.Continuum.CellGaugeAlgebra
import Maxwell.Continuum.CellBandFourierMean
import Maxwell.Continuum.BlochCellChange

/-! Exact measurable identification of the torus with the physical
period-two cell, including its mean-square measure normalization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CellGauge

open CellBandFourier MeasureTheory UnitAddTorus Set Bloch

def coordinateBox : Set (Fin 3 → ℝ) := {x | ∀ j, x j ∈ Ioc 0 (0+1)}

theorem coordinateBox_measurable : MeasurableSet coordinateBox := by
  change MeasurableSet {x : Fin 3 → ℝ | ∀ j, x j ∈ Ioc 0 (0+1)}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun j => measurableSet_Ioc.preimage (measurable_pi_apply j)

theorem unitSpatialCell_measurable : MeasurableSet unitSpatialCell := by
  change MeasurableSet {x : Space | ∀ j, x j ∈ Ioc 0 1}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun j => measurableSet_Ioc.preimage
    ((measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 (Fin 3 → ℝ)))

theorem physicalCell_measurable : MeasurableSet physicalCell := by
  have he : physicalCell = {x : Space | ∀ j, x j ∈ Ioc 0 2} := by
    ext x
    exact physicalCell_mem x
  rw [he]
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun j => measurableSet_Ioc.preimage
    ((measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 (Fin 3 → ℝ)))

theorem toLp_cell (x : Fin 3 → ℝ) :
    x ∈ coordinateBox ↔ (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) x ∈ unitSpatialCell := by
  simp only [coordinateBox, unitSpatialCell, mem_ofPred_eq, zero_add]
  rfl

def boxEuclideanEquiv : coordinateBox ≃ᵐ unitSpatialCell :=
  cellEquiv (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) coordinateBox unitSpatialCell toLp_cell

theorem boxEuclidean_measurePreserving :
    MeasurePreserving boxEuclideanEquiv (volume.comap (Subtype.val : coordinateBox → Fin 3 → ℝ))
      (volume.comap (Subtype.val : unitSpatialCell → Space)) :=
  cellEquiv_measurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
    (PiLp.volume_preserving_toLp (Fin 3)) coordinateBox unitSpatialCell
    coordinateBox_measurable unitSpatialCell_measurable toLp_cell

theorem double_cell (x : Space) : x ∈ unitSpatialCell ↔ half.symm x ∈ physicalCell := by
  rw [physicalCell_mem]
  change (∀ j, 0 < x j ∧ x j ≤ 1) ↔ (∀ j, 0 < 2 * x j ∧ 2 * x j ≤ 2)
  constructor <;> intro hx j <;> have hj := hx j <;> constructor <;> linarith

def doubleCellEquiv : unitSpatialCell ≃ᵐ physicalCell :=
  cellEquiv half.symm unitSpatialCell physicalCell double_cell

theorem doubleCell_measurePreserving :
    MeasurePreserving doubleCellEquiv (volume.comap (Subtype.val : unitSpatialCell → Space))
      ((1 / 8 : ENNReal) • (volume.comap (Subtype.val : physicalCell → Space))) := by
  have he := cellEquiv_measurePreserving half.symm half_measurePreserving.symm
    unitSpatialCell physicalCell unitSpatialCell_measurable physicalCell_measurable double_cell
  simpa only [doubleCellEquiv, Measure.comap_smul] using he

def spatialEquiv : Torus ≃ᵐ physicalCell :=
  (measurableEquivPiIoc (fun _ : Fin 3 => (0 : ℝ))).trans
    (boxEuclideanEquiv.trans doubleCellEquiv)

abbrev cellMeanMeasure : Measure physicalCell :=
  (1 / 8 : ENNReal) • (volume.comap (Subtype.val : physicalCell → Space))

theorem spatialEquiv_measurePreserving : MeasurePreserving spatialEquiv torusMeasure cellMeanMeasure :=
  doubleCell_measurePreserving.comp (boxEuclidean_measurePreserving.comp
    (measurePreserving_equivPiIoc (fun _ : Fin 3 => (0 : ℝ))))

theorem spatialEquiv_apply (t : Torus) (j : Fin 3) :
    (spatialEquiv t).val j = (cellPoint t j).val := rfl

theorem spatialEquiv_symm (x : physicalCell) : spatialEquiv.symm x = torusPoint x.val := by
  funext j
  change (((1 / 2 : ℝ) * x.val j : ℝ) : UnitAddCircle) = ((x.val j / 2 : ℝ) : UnitAddCircle)
  congr 1
  ring

abbrev PhysicalScalarCellL2 := Lp ℂ 2 cellMeanMeasure
abbrev PhysicalCellL2 := PiLp 2 (fun _ : Fin 3 => PhysicalScalarCellL2)

def scalarSpatialUnitary : PhysicalScalarCellL2 ≃ₗᵢ[ℂ] ScalarCellL2 :=
  measureEquivL2 spatialEquiv spatialEquiv_measurePreserving

def spatialUnitary : PhysicalCellL2 ≃ₗᵢ[ℂ] CellFieldL2 :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 3 => scalarSpatialUnitary)

theorem spatialUnitary_ae (u : PhysicalCellL2) (j : Fin 3) :
    spatialUnitary u j =ᵐ[torusMeasure] fun t => u j (spatialEquiv t) :=
  measureEquivL2_ae spatialEquiv spatialEquiv_measurePreserving (u j)

theorem spatialUnitary_norm (u : PhysicalCellL2) : ‖spatialUnitary u‖ = ‖u‖ := spatialUnitary.norm_map u

#print axioms spatialEquiv_measurePreserving
#print axioms spatialUnitary_ae
#print axioms spatialUnitary_norm

end Maxwell.Continuum.CellGauge
