import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp

/-! Exact finite identities used by the logical and physical reductions.

The inverse and nonzero hypotheses below are explicit local algebraic premises.
This module does not assume, or claim to prove, physical existence or norm bounds.
-/

namespace Maxwell

open Matrix
open scoped Matrix

section Blocks

variable {m n R : Type*} [Fintype m] [Fintype n] [CommRing R]

/-- Exact elimination of arbitrary residuals, including mediator-source errors. -/
theorem schur_residual_identity [DecidableEq n]
    (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R)
    (D X : Matrix n n R) (hXD : X * D = 1)
    (x : m → R) (y : n → R) (f : m → R) (g : n → R) :
    (A - B * X * C) *ᵥ x - (f - (B * X) *ᵥ g) =
      (A *ᵥ x + B *ᵥ y - f) - (B * X) *ᵥ (C *ᵥ x + D *ᵥ y - g) := by
  have hcancel : (B * X) *ᵥ (D *ᵥ y) = B *ᵥ y := by
    rw [mulVec_mulVec, Matrix.mul_assoc, hXD, Matrix.mul_one]
  rw [sub_mulVec, mulVec_sub, mulVec_add, hcancel, mulVec_mulVec]
  abel

/-- The full block factorization keeps the entire operator in the statement. -/
theorem full_block_factorization [DecidableEq m] [DecidableEq n]
    (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R)
    (D : Matrix n n R) [Invertible D] :
    fromBlocks A B C D =
      fromBlocks 1 (B * ⅟D) 0 1 *
        fromBlocks (A - B * ⅟D * C) 0 0 D *
        fromBlocks 1 0 (⅟D * C) 1 :=
  Matrix.fromBlocks_eq_of_invertible₂₂ A B C D

/-- Symmetrization preserves the original equation residual in the first block. -/
theorem symmetrization_residual
    (H : Matrix m n R) (v : m → R) (z : n → R) (h : m → R) (i : m) :
    ((fromBlocks 0 H H.transpose 0) *ᵥ (Sum.elim v z) -
      Sum.elim h (0 : n → R)) (Sum.inl i) = (H *ᵥ z - h) i := by
  simp [Matrix.fromBlocks_mulVec]

/-- The sparse saddle system eliminates to the normal equation exactly,
without assuming its approximate solution has zero auxiliary residual. -/
theorem saddle_normal_residual
    (F : Matrix m n R) (y : m → R) (z q : n → R) :
    (F.transpose * F) *ᵥ z - q =
      F.transpose *ᵥ (y + F *ᵥ z) - (F.transpose *ᵥ y + q) := by
  rw [mulVec_add, mulVec_mulVec]
  abel

/-- Exact projected-error identity used in the unrestricted-real transfer. -/
theorem saddle_projected_error [DecidableEq n]
    (F : Matrix m n R) (X : Matrix n n R)
    (hX : X * (F.transpose * F) = 1)
    (y : m → R) (z zstar q : n → R)
    (hstar : (F.transpose * F) *ᵥ zstar = q) :
    F *ᵥ (z - zstar) =
      (F * X * F.transpose) *ᵥ (y + F *ᵥ z) -
        (F * X) *ᵥ (F.transpose *ᵥ y + q) := by
  have hid : (F * X) * (F.transpose * F) = F := by
    rw [Matrix.mul_assoc, hX, Matrix.mul_one]
  rw [← mulVec_mulVec, ← mulVec_sub,
    ← saddle_normal_residual, ← hstar, ← mulVec_sub, mulVec_mulVec, hid]

end Blocks

/-- Exact arithmetic of a signed logical mediator. -/
theorem signed_mediator_schur (w : ℚ) (hw : w ≠ 0) :
    -(1 / (-1 / w)) = w := by
  field_simp

/-- The physical mediator diagonal produces the prescribed coupling.
The identity is valid over either rational or real scalar fields. -/
theorem physical_mediator_schur {K : Type*} [Field K]
    (alpha beta : K) (ha : alpha ≠ 0) (hb : beta ≠ 0) :
    -(beta * (1 / (-(beta * beta) / alpha)) * beta) = alpha := by
  field_simp

end Maxwell
