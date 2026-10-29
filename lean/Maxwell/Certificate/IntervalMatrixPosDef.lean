import Maxwell.Certificate.IntervalMatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Strict pivot interval certificates certify positive definiteness. -/

noncomputable section

namespace Maxwell.Certificate.SchurStep

open Matrix
open scoped ComplexOrder

/-- A strictly positive pivot and positive definite Schur complement certify
positive definiteness, including the last scalar pivot. -/
theorem posDef_of_schur {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsHermitian)
    (hd : 0 < (A 0 0).re) (hS : (schur A).PosDef) : A.PosDef := by
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
  have hblockPSD : (Matrix.fromBlocks D B Bᴴ C).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ B C hD).mpr (hSC.symm ▸ hS.posSemidef)
  have hblockUnit : IsUnit (Matrix.fromBlocks D B Bᴴ C) := by
    apply Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mpr
    rw [Matrix.invOf_eq_nonsing_inv, hSC]
    exact hS.isUnit
  have hblock : (Matrix.fromBlocks D B Bᴴ C).PosDef :=
    hblockPSD.posDef_iff_isUnit.mpr hblockUnit
  let f : Fin (n + 1) → Unit ⊕ Fin n := Fin.cases (Sum.inl ()) Sum.inr
  have hf : Function.Injective f := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    · intro _; rfl
    · simp [f]
    · simp [f]
    · intro hij
      exact congrArg Fin.succ (Sum.inr.inj hij)
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
  exact hblock.submatrix hf

end Maxwell.Certificate.SchurStep

namespace Maxwell.Certificate.IntervalMatrix

open scoped ComplexOrder

/-- Acceptance of the recursive strict-pivot certificate proves positive
definiteness of every enclosed Hermitian matrix. -/
theorem accepts_posDef {n : ℕ} {a : Enclosure n} (w : Proposal n)
    (h : accepts a w = true) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (ha : Contains a A) : A.PosDef := by
  induction w with
  | empty =>
      apply Matrix.PosDef.of_dotProduct_mulVec_pos hA
      intro x hx
      exact (hx (funext fun i => Fin.elim0 i)).elim
  | @next n b tail ih =>
      simp only [accepts] at h
      split_ifs at h with hp
      · have hh := Bool.and_eq_true_iff.mp h
        apply SchurStep.posDef_of_schur hA (positive_pivot hp ha)
        exact ih hh.2 (SchurStep.schur_isHermitian hA)
          (subsetCheck_sound hh.1 (step_contains hp ha))

/-- The lower-triangle certificate has the same strict conclusion. -/
theorem accepts_lower_posDef {n : ℕ} {a : Enclosure n} (w : Proposal n)
    (h : accepts (hermitianCompletion a) w = true)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (ha : LowerContains a A) :
    A.PosDef := accepts_posDef w h hA (hermitianCompletion_contains hA ha)

end Maxwell.Certificate.IntervalMatrix
