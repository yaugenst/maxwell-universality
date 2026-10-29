import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.BigOperators.Fin

namespace Maxwell.Spectral

open scoped BigOperators Matrix

variable {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
variable [DecidableEq α] [DecidableEq ι] [DecidableEq κ]

/-- Concatenation of the four (or any finite number of) sector lifts. -/
def sectorLift (L : α → Matrix κ ι ℂ) : Matrix κ (ι × α) ℂ :=
  fun i j => L j.2 i j.1

def sectorDiagonal (B : α → Matrix ι ι ℂ) : Matrix (ι × α) (ι × α) ℂ :=
  fun i j => if i.2 = j.2 then B i.2 i.1 j.1 else 0

omit [DecidableEq ι] [DecidableEq κ] in
/-- Genuine sectorwise intertwining gives full block intertwining. -/
theorem sectorLift_intertwining (A : Matrix κ κ ℂ) (L : α → Matrix κ ι ℂ)
    (B : α → Matrix ι ι ℂ) (h : ∀ a, A * L a = L a * B a) :
    A * sectorLift L = sectorLift L * sectorDiagonal B := by
  ext i j
  rcases j with ⟨j, a⟩
  have hj := congrArg (fun M : Matrix κ ι ℂ => M i j) (h a)
  simpa [Matrix.mul_apply, sectorLift, sectorDiagonal, Fintype.sum_prod_type,
    mul_ite, Finset.sum_ite_eq'] using hj

omit [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι] [DecidableEq κ] in
/-- Every Gram block is the actual inner product of two lifts. -/
theorem sectorLift_gram_block (L : α → Matrix κ ι ℂ)
    (a b : α) (i j : ι) :
    ((sectorLift L).conjTranspose * sectorLift L) (i, a) (j, b) =
      ((L a).conjTranspose * L b) i j := by
  simp [Matrix.mul_apply, sectorLift, Matrix.conjTranspose_apply]

omit [Fintype α] [Fintype ι] [DecidableEq κ] in
/-- Mutually orthogonal isometric sector lifts assemble to an isometry. -/
theorem sectorLift_gram_identity (L : α → Matrix κ ι ℂ)
    (h : ∀ a b, (L a).conjTranspose * L b = if a = b then 1 else 0) :
    (sectorLift L).conjTranspose * sectorLift L = 1 := by
  ext i j
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  rw [sectorLift_gram_block, h]
  by_cases hab : a = b
  · subst b
    simp [Matrix.one_apply]
  · simp [hab]

omit [DecidableEq κ] in
/-- The transformed conventional operator is the direct sum of the actual
primitive sectors once their normalized lift is isometric. -/
theorem sectorLift_folding (A : Matrix κ κ ℂ) (L : α → Matrix κ ι ℂ)
    (B : α → Matrix ι ι ℂ) (h : ∀ a, A * L a = L a * B a)
    (hunit : (sectorLift L).conjTranspose * sectorLift L = 1) :
    (sectorLift L).conjTranspose * A * sectorLift L = sectorDiagonal B := by
  rw [Matrix.mul_assoc, sectorLift_intertwining A L B h,
    ← Matrix.mul_assoc, hunit, Matrix.one_mul]

end Maxwell.Spectral
