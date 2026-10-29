import Maxwell.Defect.FiniteStencil
import Maxwell.Spectral.Concrete

/-! The finite rational stencil specialized to the frozen material. -/

namespace Maxwell.Defect.FiniteStencil

open Spectral Spectral.Lattice

/-- Keep the fixed 8000-cell lookup shared during elaboration and execution. -/
@[irreducible, noinline] def frozenMaterialQ (r : Lattice.Cell20) : ℚ :=
  Certificate.Material.cellValue (fun j => ⟨(r j).val, ZMod.val_lt (r j)⟩)

def rationalEdgeAverage (material : Lattice.Cell20 → ℚ) (e : Edge) : ℚ :=
  let r := siteMod20 e.2
  let p := PeriodicYee.transverseDirections e.1
  (material r + material (r - PeriodicYee.unitCell p.1) +
    material (r - PeriodicYee.unitCell p.2) +
    material (r - PeriodicYee.unitCell p.1 - PeriodicYee.unitCell p.2)) / 4

def frozenEdgeCoefficientQ : Edge → ℚ := rationalEdgeAverage frozenMaterialQ

theorem frozenMaterialQ_binding (r : Lattice.Cell20) :
    (frozenMaterialQ r : ℝ) = Concrete.material r := by
  unfold frozenMaterialQ
  rfl

theorem frozenEdgeCoefficientQ_binding (e : Edge) :
    (frozenEdgeCoefficientQ e : ℝ) =
      periodicCoefficient (PeriodicYee.edgeAverage Concrete.material) e := by
  simp only [frozenEdgeCoefficientQ, rationalEdgeAverage, periodicCoefficient, edgeMod20,
    PeriodicYee.edgeAverage, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat,
    frozenMaterialQ_binding]

theorem frozenEdgeCoefficientQ_bounds (e : Edge) :
    1 ≤ (frozenEdgeCoefficientQ e : ℝ) ∧ (frozenEdgeCoefficientQ e : ℝ) ≤ 13 := by
  rw [frozenEdgeCoefficientQ_binding]
  exact PeriodicYee.edgeAverage_bounds Concrete.material 1 13
    (fun r => ⟨(Concrete.material_bounds r).1, (Concrete.material_bounds r).2.le⟩) _

theorem frozenEdgeCoefficientQ_abs (e : Edge) : |(frozenEdgeCoefficientQ e : ℝ)| ≤ 13 := by
  rw [abs_of_nonneg (le_trans (by norm_num) (frozenEdgeCoefficientQ_bounds e).1)]
  exact (frozenEdgeCoefficientQ_bounds e).2

noncomputable def frozenOperator (z : ℚ) : Field →L[ℂ] Field :=
  operator frozenEdgeCoefficientQ 13 (by norm_num) frozenEdgeCoefficientQ_abs z

def frozenInverseAction (z s : ℚ) (N : ℕ) (v : SparseField) : SparseField :=
  inverseAction frozenEdgeCoefficientQ z s N v

theorem embed_frozenInverseAction (z s : ℚ) (N : ℕ) (v : SparseField) :
    embed (frozenInverseAction z s N v) =
      inversePolynomial (frozenOperator z) (s : ℂ) N (embed v) :=
  embed_inverseAction frozenEdgeCoefficientQ 13 (by norm_num) frozenEdgeCoefficientQ_abs z s N v

theorem frozenOperator_binding (z : ℚ) :
    frozenOperator z = electricOperator
      (periodicCoefficient (PeriodicYee.edgeAverage Concrete.material)) 13
      (by norm_num) (fun e => by rw [← frozenEdgeCoefficientQ_binding]; exact frozenEdgeCoefficientQ_abs e) -
        (z : ℂ) • ContinuousLinearMap.id ℂ Field := by
  unfold frozenOperator operator
  have hm : (fun e => (frozenEdgeCoefficientQ e : ℝ)) =
      periodicCoefficient (PeriodicYee.edgeAverage Concrete.material) :=
    funext frozenEdgeCoefficientQ_binding
  simp only [hm]

end Maxwell.Defect.FiniteStencil
