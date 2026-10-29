import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! A single exact Hermitian Schur step for recursive interval certificates. -/

noncomputable section

namespace Maxwell.Certificate.SchurStep

open Matrix
open scoped ComplexOrder

def schur {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => A i.succ j.succ -
    A i.succ 0 * star (A j.succ 0) / ((A 0 0).re : ℂ)

theorem schur_isHermitian {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsHermitian) :
    (schur A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [schur, hA.apply, mul_comm]

theorem diagonal_eq_real {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsHermitian) :
    A 0 0 = ((A 0 0).re : ℂ) := by
  have him : (A 0 0).im = 0 :=
    (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr (hA.apply 0 0)
  exact Complex.ext rfl him

/-- A positive first pivot and a positive semidefinite exact Schur
complement certify the entire Hermitian matrix, including the scalar case. -/
theorem posSemidef_of_schur {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsHermitian)
    (hd : 0 < (A 0 0).re) (hS : (schur A).PosSemidef) : A.PosSemidef := by
  let D : Matrix Unit Unit ℂ := diagonal fun _ => ((A 0 0).re : ℂ)
  let B : Matrix Unit (Fin n) ℂ := fun _ j => A 0 j.succ
  let C : Matrix (Fin n) (Fin n) ℂ := A.submatrix Fin.succ Fin.succ
  have hD : D.PosDef := Matrix.PosDef.diagonal fun _ => Complex.zero_lt_real.mpr hd
  let _ := hD.isUnit.invertible
  have hSC : C - Bᴴ * D⁻¹ * B = schur A := by
    ext i j
    change A i.succ j.succ -
      (∑ u : Unit, (∑ v : Unit, star (A 0 i.succ) * D⁻¹ v u) * A 0 j.succ) = _
    simp only [Fintype.sum_unique, Matrix.inv_subsingleton, D,
      Matrix.diagonal_apply_eq, Ring.inverse_eq_inv, schur, hA.apply, div_eq_mul_inv]
    ring
  have hblock : (Matrix.fromBlocks D B Bᴴ C).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ B C hD).mpr (hSC.symm ▸ hS)
  let f : Fin (n + 1) → Unit ⊕ Fin n := Fin.cases (Sum.inl ()) Sum.inr
  have heq : (Matrix.fromBlocks D B Bᴴ C).submatrix f f = A := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    · simpa [f, D] using (diagonal_eq_real hA).symm
    · rfl
    · change star (A 0 i.succ) = A i.succ 0
      exact hA.apply i.succ 0
    · simp [f, C]
  rw [← heq]
  exact hblock.submatrix f

end Maxwell.Certificate.SchurStep
