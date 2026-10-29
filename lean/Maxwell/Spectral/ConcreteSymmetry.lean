import Maxwell.Spectral.Concrete
import Maxwell.Certificate.MaterialSymmetry
import Maxwell.Spectral.PrimitiveYee
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.FinCases

namespace Maxwell.Spectral.Concrete

open PeriodicYee

theorem cellCoordinate_vector (r : Cell20) :
    cellCoordinate r = ![cellCoordinate r 0, cellCoordinate r 1, cellCoordinate r 2] := by
  funext j
  fin_cases j <;> rfl

theorem material_fcc_periodicity (r : Cell20) :
    material (r + ![0, 10, 10]) = material r ∧
    material (r + ![10, 0, 10]) = material r ∧
    material (r + ![10, 10, 0]) = material r := by
  have hv : (10 : ZMod 20).val = 10 := by decide
  have h := Maxwell.Certificate.Material.cellValue_fcc_periodicity
    (cellCoordinate r 0) (cellCoordinate r 1) (cellCoordinate r 2)
  have h1 : cellCoordinate (r + ![0, 10, 10]) =
      ![cellCoordinate r 0, Maxwell.Certificate.Material.halfShift (cellCoordinate r 1),
        Maxwell.Certificate.Material.halfShift (cellCoordinate r 2)] := by
    funext j
    fin_cases j <;> apply Fin.ext <;>
      simp [cellCoordinate, Maxwell.Certificate.Material.halfShift, ZMod.val_add, hv]
  have h2 : cellCoordinate (r + ![10, 0, 10]) =
      ![Maxwell.Certificate.Material.halfShift (cellCoordinate r 0), cellCoordinate r 1,
        Maxwell.Certificate.Material.halfShift (cellCoordinate r 2)] := by
    funext j
    fin_cases j <;> apply Fin.ext <;>
      simp [cellCoordinate, Maxwell.Certificate.Material.halfShift, ZMod.val_add, hv]
  have h3 : cellCoordinate (r + ![10, 10, 0]) =
      ![Maxwell.Certificate.Material.halfShift (cellCoordinate r 0),
        Maxwell.Certificate.Material.halfShift (cellCoordinate r 1), cellCoordinate r 2] := by
    funext j
    fin_cases j <;> apply Fin.ext <;>
      simp [cellCoordinate, Maxwell.Certificate.Material.halfShift, ZMod.val_add, hv]
  unfold material
  rw [h1, h2, h3, h.1, h.2.1, h.2.2, cellCoordinate_vector r]
  exact ⟨rfl, rfl, rfl⟩

theorem material_lattice_periodicity (r : PrimitiveYee.RawCell)
    (n : PrimitiveYee.Translation) :
    material (PrimitiveYee.conventionalCell (r + PrimitiveYee.latticeVector n)) =
      material (PrimitiveYee.conventionalCell r) := by
  have hxy : Function.Periodic material (![10, 10, 0] : Cell20) :=
    fun r => (material_fcc_periodicity r).2.2
  have hxz : Function.Periodic material (![10, 0, 10] : Cell20) :=
    fun r => (material_fcc_periodicity r).2.1
  have hvec : PrimitiveYee.conventionalCell (PrimitiveYee.latticeVector n) =
      (n 1) • (![10, 10, 0] : Cell20) + (n 2) • (![10, 0, 10] : Cell20) := by
    have hz : (20 : ZMod 20) = 0 := by decide
    funext j
    fin_cases j <;>
      simp [PrimitiveYee.conventionalCell, PrimitiveYee.latticeVector,
        Pi.add_apply, zsmul_eq_mul, hz] <;> ring
  rw [PrimitiveYee.conventionalCell_add, hvec]
  exact ((hxy.zsmul (n 1)).add_period (hxz.zsmul (n 2))) _

theorem material_inversion (r : Cell20) : material (-r - 1) = material r := by
  have hv : (-1 : ZMod 20).val = 19 := by decide
  have hc : cellCoordinate (-r - 1) =
      ![Maxwell.Certificate.Material.invertCell (cellCoordinate r 0),
        Maxwell.Certificate.Material.invertCell (cellCoordinate r 1),
        Maxwell.Certificate.Material.invertCell (cellCoordinate r 2)] := by
    have hall (j : Direction) : ((-r - 1) j).val = 19 - (r j).val := by
      have hb : (r j).val ≤ (-1 : ZMod 20).val := by
        rw [hv]
        have hlt := ZMod.val_lt (r j)
        omega
      change (-r j - 1).val = _
      rw [show -r j - 1 = (-1 : ZMod 20) - r j by ring, ZMod.val_sub hb, hv]
    funext j
    fin_cases j <;> apply Fin.ext <;>
      simpa [cellCoordinate, Maxwell.Certificate.Material.invertCell] using hall _
  unfold material
  rw [hc, Maxwell.Certificate.Material.cellValue_inversion, cellCoordinate_vector r]
  simp

theorem edgeAverage_inversion (j : Direction) (r : Cell20) :
    PeriodicYee.edgeAverage material (j, -r - unitCell j) =
      PeriodicYee.edgeAverage material (j, r) := by
  let a := (transverseDirections j).1
  let b := (transverseDirections j).2
  have hsum : unitCell j + unitCell a + unitCell b = (1 : Cell20) := by
    funext l
    fin_cases j <;> fin_cases l <;> norm_num [a, b, transverseDirections, unitCell]
  have h0 : -r - unitCell j = -(r - unitCell a - unitCell b) - 1 := by
    rw [← hsum]
    abel
  have ha : -r - unitCell j - unitCell a = -(r - unitCell b) - 1 := by
    rw [← hsum]
    abel
  have hb : -r - unitCell j - unitCell b = -(r - unitCell a) - 1 := by
    rw [← hsum]
    abel
  have hab : -r - unitCell j - unitCell a - unitCell b = -r - 1 := by
    rw [← hsum]
    abel
  change (material (-r - unitCell j) + material (-r - unitCell j - unitCell a) +
      material (-r - unitCell j - unitCell b) +
      material (-r - unitCell j - unitCell a - unitCell b)) / 4 =
    (material r + material (r - unitCell a) + material (r - unitCell b) +
      material (r - unitCell a - unitCell b)) / 4
  rw [hab, ha, hb, h0, material_inversion, material_inversion,
    material_inversion, material_inversion]
  ring

theorem edgeAverage_raw_inversion (j : Direction) (r : PrimitiveYee.RawCell) :
    PeriodicYee.edgeAverage material
      (j, PrimitiveYee.conventionalCell (-r - PrimitiveYee.rawUnit j)) =
      PeriodicYee.edgeAverage material (j, PrimitiveYee.conventionalCell r) := by
  rw [PrimitiveYee.conventionalCell_sub, PrimitiveYee.conventionalCell_rawUnit]
  have hneg : PrimitiveYee.conventionalCell (-r) = -PrimitiveYee.conventionalCell r := by
    funext l
    simp [PrimitiveYee.conventionalCell]
  rw [hneg]
  exact edgeAverage_inversion j _

theorem edgeAverage_lattice_periodicity (j : Direction) (r : PrimitiveYee.RawCell)
    (n : PrimitiveYee.Translation) :
    PeriodicYee.edgeAverage material
      (j, PrimitiveYee.conventionalCell (r + PrimitiveYee.latticeVector n)) =
      PeriodicYee.edgeAverage material (j, PrimitiveYee.conventionalCell r) := by
  have hshift (s : PrimitiveYee.RawCell) :
      r + PrimitiveYee.latticeVector n - s = (r - s) + PrimitiveYee.latticeVector n := by abel
  unfold PeriodicYee.edgeAverage
  simp only [← PrimitiveYee.conventionalCell_rawUnit, ← PrimitiveYee.conventionalCell_sub]
  rw [material_lattice_periodicity, hshift, material_lattice_periodicity, hshift,
    material_lattice_periodicity]
  congr 2
  have heq : r - PrimitiveYee.rawUnit (transverseDirections j).1 +
      PrimitiveYee.latticeVector n -
      PrimitiveYee.rawUnit (transverseDirections j).2 =
      (r - PrimitiveYee.rawUnit (transverseDirections j).1 -
      PrimitiveYee.rawUnit (transverseDirections j).2) + PrimitiveYee.latticeVector n := by abel
  rw [heq, material_lattice_periodicity]

theorem edgeAverage_reduce (j : Direction) (r : PrimitiveYee.RawCell) :
    PeriodicYee.edgeAverage material
      (j, PrimitiveYee.conventionalCell (PrimitiveYee.representative (PrimitiveYee.reduceCell r))) =
      PeriodicYee.edgeAverage material (j, PrimitiveYee.conventionalCell r) := by
  have h := edgeAverage_lattice_periodicity j
    (PrimitiveYee.representative (PrimitiveYee.reduceCell r)) (PrimitiveYee.reduceTranslation r)
  change PeriodicYee.edgeAverage material
    (j, PrimitiveYee.conventionalCell (PrimitiveYee.reconstruct (PrimitiveYee.reduceCell r)
      (PrimitiveYee.reduceTranslation r))) = _ at h
  rw [PrimitiveYee.reconstruct_reduce] at h
  exact h.symm

theorem primitiveEdgeAverage_inversion (j : Direction) (p : PrimitiveYee.Cell) :
    PrimitiveYee.edgeAverage material
      (j, PrimitiveYee.reduceCell (-PrimitiveYee.representative p - PrimitiveYee.rawUnit j)) =
      PrimitiveYee.edgeAverage material (j, p) := by
  rw [PrimitiveYee.edgeAverage_binding, edgeAverage_reduce, edgeAverage_raw_inversion,
    PrimitiveYee.edgeAverage_binding]

end Maxwell.Spectral.Concrete
