import Maxwell.Spectral.GlobalCubic.CellAction
import Maxwell.Spectral.ConcreteSymmetry
import Maxwell.Certificate.MaterialBaseCubic

namespace Maxwell.Spectral.GlobalCubic

open PeriodicYee
open PrimitiveYee (RawCell rawUnit conventionalCell)
open Concrete (cellCoordinate baseMaterial)
noncomputable section

theorem baseMaterial_fcc_periodicity (r : Cell20) :
    baseMaterial (r + ![0,10,10]) = baseMaterial r ∧
    baseMaterial (r + ![10,0,10]) = baseMaterial r ∧
    baseMaterial (r + ![10,10,0]) = baseMaterial r := by
  have hv : (10 : ZMod 20).val = 10 := by decide
  have h := Maxwell.Certificate.Material.base_fcc_periodicity
    (cellCoordinate r 0) (cellCoordinate r 1) (cellCoordinate r 2)
  have h1 : cellCoordinate (r + ![0,10,10]) =
      ![cellCoordinate r 0, Maxwell.Certificate.Material.halfShift (cellCoordinate r 1),
        Maxwell.Certificate.Material.halfShift (cellCoordinate r 2)] := by
    funext j
    fin_cases j <;> apply Fin.ext <;>
      simp [cellCoordinate, Maxwell.Certificate.Material.halfShift, ZMod.val_add, hv]
  have h2 : cellCoordinate (r + ![10,0,10]) =
      ![Maxwell.Certificate.Material.halfShift (cellCoordinate r 0), cellCoordinate r 1,
        Maxwell.Certificate.Material.halfShift (cellCoordinate r 2)] := by
    funext j
    fin_cases j <;> apply Fin.ext <;>
      simp [cellCoordinate, Maxwell.Certificate.Material.halfShift, ZMod.val_add, hv]
  have h3 : cellCoordinate (r + ![10,10,0]) =
      ![Maxwell.Certificate.Material.halfShift (cellCoordinate r 0),
        Maxwell.Certificate.Material.halfShift (cellCoordinate r 1), cellCoordinate r 2] := by
    funext j
    fin_cases j <;> apply Fin.ext <;>
      simp [cellCoordinate, Maxwell.Certificate.Material.halfShift, ZMod.val_add, hv]
  unfold baseMaterial
  rw [h1,h2,h3,h.1,h.2.1,h.2.2,Concrete.cellCoordinate_vector r]
  exact ⟨rfl,rfl,rfl⟩

theorem baseMaterial_FCCPeriodic : Folding.FCCPeriodic baseMaterial := by
  intro r n
  have hxy : Function.Periodic baseMaterial (![10,10,0] : Cell20) :=
    fun r => (baseMaterial_fcc_periodicity r).2.2
  have hxz : Function.Periodic baseMaterial (![10,0,10] : Cell20) :=
    fun r => (baseMaterial_fcc_periodicity r).2.1
  have hvec : conventionalCell (PrimitiveYee.latticeVector n) =
      (n 1) • (![10,10,0] : Cell20) + (n 2) • (![10,0,10] : Cell20) := by
    have hz : (20 : ZMod 20) = 0 := by decide
    funext j
    fin_cases j <;> simp [conventionalCell, PrimitiveYee.latticeVector,
      Pi.add_apply, zsmul_eq_mul, hz] <;> ring
  rw [PrimitiveYee.conventionalCell_add, hvec]
  exact ((hxy.zsmul (n 1)).add_period (hxz.zsmul (n 2))) _

theorem shiftedBase_FCCPeriodic (c : ℝ) :
    Folding.FCCPeriodic (fun r => baseMaterial r+c) := by
  intro r n
  change baseMaterial (conventionalCell (r+PrimitiveYee.latticeVector n))+c =
    baseMaterial (conventionalCell r)+c
  rw [baseMaterial_FCCPeriodic r n]

theorem cellCoordinate_reflect (r : RawCell) :
    cellCoordinate (conventionalCell (cellAction .reflect0 5 r)) =
      ![Maxwell.Certificate.Material.invertCell (cellCoordinate (conventionalCell r) 0),
        Maxwell.Certificate.Material.quarterShift (cellCoordinate (conventionalCell r) 1),
        Maxwell.Certificate.Material.quarterShift (cellCoordinate (conventionalCell r) 2)] := by
  have hv : (-1 : ZMod 20).val = 19 := by decide
  have h5 : (5 : ZMod 20).val = 5 := by decide
  have h0 : ((-r 0-1 : ℤ) : ZMod 20).val = 19-(r 0 : ZMod 20).val := by
    have hb : (r 0 : ZMod 20).val ≤ (-1 : ZMod 20).val := by
      rw [hv]
      have hlt := ZMod.val_lt (r 0 : ZMod 20)
      omega
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_one]
    rw [show -(r 0 : ZMod 20)-1 = -1-(r 0 : ZMod 20) by ring, ZMod.val_sub hb, hv]
  funext j
  fin_cases j <;> apply Fin.ext
  · simpa [cellCoordinate, conventionalCell, cellAction, node, linear, rawUnit,
      Maxwell.Certificate.Material.invertCell] using h0
  · simp [cellCoordinate, conventionalCell, cellAction, node, linear, rawUnit,
      Maxwell.Certificate.Material.quarterShift, ZMod.val_add, h5]
  · simp [cellCoordinate, conventionalCell, cellAction, node, linear, rawUnit,
      Maxwell.Certificate.Material.quarterShift, ZMod.val_add, h5]

theorem baseMaterial_cellAction (g : Generator) (r : RawCell) :
    baseMaterial (conventionalCell (cellAction g 5 r)) = baseMaterial (conventionalCell r) := by
  cases g with
  | swap01 =>
    have hc : cellCoordinate (conventionalCell (cellAction .swap01 5 r)) =
        ![cellCoordinate (conventionalCell r) 1, cellCoordinate (conventionalCell r) 0,
          cellCoordinate (conventionalCell r) 2] := by
      funext j
      fin_cases j <;> simp [cellCoordinate, conventionalCell, cellAction, node, linear]
    unfold baseMaterial
    rw [hc, Maxwell.Certificate.Material.base_swap01, Concrete.cellCoordinate_vector]
    rfl
  | swap12 =>
    have hc : cellCoordinate (conventionalCell (cellAction .swap12 5 r)) =
        ![cellCoordinate (conventionalCell r) 0, cellCoordinate (conventionalCell r) 2,
          cellCoordinate (conventionalCell r) 1] := by
      funext j
      fin_cases j <;> simp [cellCoordinate, conventionalCell, cellAction, node, linear]
    unfold baseMaterial
    rw [hc, Maxwell.Certificate.Material.base_swap12, Concrete.cellCoordinate_vector]
    rfl
  | reflect0 =>
    unfold baseMaterial
    rw [cellCoordinate_reflect, Maxwell.Certificate.Material.base_glide0,
      Concrete.cellCoordinate_vector]
    rfl

theorem shiftedBase_cellAction (c : ℝ) (g : Generator) (r : RawCell) :
    baseMaterial (conventionalCell (cellAction g 5 r))+c = baseMaterial (conventionalCell r)+c := by
  rw [baseMaterial_cellAction]

theorem base_shift_fcc (c : ℝ) : Folding.FCCPeriodic (fun r => baseMaterial r+c) :=
  shiftedBase_FCCPeriodic c

theorem base_shift_scalar_symmetry (c : ℝ) (g : Generator) (r : RawCell) :
    (fun x => baseMaterial x+c) (conventionalCell (cellAction g 5 r)) =
      (fun x => baseMaterial x+c) (conventionalCell r) :=
  shiftedBase_cellAction c g r

end
end Maxwell.Spectral.GlobalCubic
