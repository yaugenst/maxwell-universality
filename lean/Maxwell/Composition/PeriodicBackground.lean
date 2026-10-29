import Maxwell.Composition.PhysicalPlatform

/-! The platform's periodic scalar cells and the finite PEC four-cell
average define exactly the same infinite operating operator. -/
noncomputable section
namespace Maxwell.Composition.PeriodicScalarBackground
open Maxwell.Spectral Maxwell.Spectral.Lattice

theorem siteMod20_add (x y : Site) : siteMod20 (x + y) = siteMod20 x + siteMod20 y := by
  ext k
  simp [siteMod20]

theorem siteMod20_sub (x y : Site) : siteMod20 (x - y) = siteMod20 x - siteMod20 y := by
  ext k
  simp [siteMod20]

theorem siteMod20_unit (j : Direction) : siteMod20 (unitSite j) = PeriodicYee.unitCell j := by
  ext k
  by_cases h : k = j <;> simp [siteMod20, unitSite, PeriodicYee.unitCell, h]

theorem lattice_average (P : PeriodicScalarBackground) (e : Edge) :
    Target.latticeEdgeAverage P.scalar e = periodicCoefficient P.edgeMaterial e := by
  unfold Target.latticeEdgeAverage
  simp only [TranslatedStencil.incidentCell_order]
  simp only [scalar, Maxwell.Defect.ScalarDefect.incidentCell,
    Maxwell.Defect.ScalarDefect.incidentOffset]
  change ((P.material (siteMod20 (e.2 - (unitSite (PeriodicYee.transverseDirections e.1).1 +
        unitSite (PeriodicYee.transverseDirections e.1).2))) : ℝ) +
    P.material (siteMod20 (e.2 - unitSite (PeriodicYee.transverseDirections e.1).2)) +
    P.material (siteMod20 (e.2 - unitSite (PeriodicYee.transverseDirections e.1).1)) +
    P.material (siteMod20 (e.2 - 0))) / 4 = _
  simp only [siteMod20_sub, siteMod20_add, siteMod20_unit, sub_zero]
  change ((P.material (siteMod20 e.2 - (PeriodicYee.unitCell (PeriodicYee.transverseDirections e.1).1 +
      PeriodicYee.unitCell (PeriodicYee.transverseDirections e.1).2)) : ℝ) +
    P.material (siteMod20 e.2 - PeriodicYee.unitCell (PeriodicYee.transverseDirections e.1).2) +
    P.material (siteMod20 e.2 - PeriodicYee.unitCell (PeriodicYee.transverseDirections e.1).1) +
    P.material (siteMod20 e.2)) / 4 = _
  simp only [sub_add_eq_sub_sub]
  dsimp [periodicCoefficient, edgeMaterial, PeriodicYee.edgeAverage, edgeMod20]
  ring

theorem operator_lattice (P : PeriodicScalarBackground)
    (M : ℝ) (hM : 0 ≤ M) (hm : ∀ e, |Target.latticeEdgeAverage P.scalar e| ≤ M) :
    P.operator = electricOperator (Target.latticeEdgeAverage P.scalar) M hM hm := by
  have he : Target.latticeEdgeAverage P.scalar = periodicCoefficient P.edgeMaterial :=
    funext P.lattice_average
  have ht : realSequenceMultiplier (periodicCoefficient P.edgeMaterial) 25 (by norm_num) P.edge_bound =
      realSequenceMultiplier (Target.latticeEdgeAverage P.scalar) M hM hm := by
    ext x e
    simp only [realSequenceMultiplier_apply, he]
  exact congrArg (fun T : Field →L[ℂ] Field => yeeCurl.adjoint.comp yeeCurl - (1 / 64 : ℂ) • T) ht

theorem bulk_inverse_eq (P : PhysicalPlatform) :
    (P.bulk.symm : Field →L[ℂ] Field) = Ring.inverse P.background.operator := by
  rw [← P.bulk_operator]
  exact (Ring.inverse_unit P.bulk.toUnit).symm

end Maxwell.Composition.PeriodicScalarBackground
