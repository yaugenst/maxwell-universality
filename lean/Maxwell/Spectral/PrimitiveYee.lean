import Maxwell.Spectral.PeriodicYee
import Mathlib.LinearAlgebra.Matrix.Notation
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The primitive FCC Yee cell

The lattice basis is `(20,0,0),(10,10,0),(10,0,10)` and the representatives
are `[0,20) × [0,10) × [0,10)`.  Coordinate reduction below is the integer
algorithm in `exact_edge_arithmetic.py`, including its floor division for
negative coordinates.  The reconstruction identities prove that no cell is
lost or counted twice.  The difference, curl, and mass are the actual Yee
stencils on these representatives, rather than abstract certificate matrices.
-/

namespace Maxwell.Spectral.PrimitiveYee

open PeriodicYee
open scoped Matrix

abbrev Cell := Fin 20 × Fin 10 × Fin 10
abbrev Electric := Direction × Cell
abbrev Face := Direction × Cell
abbrev RawCell := Direction → ℤ
abbrev Translation := Direction → ℤ

def representative (p : Cell) : RawCell := ![p.1.val, p.2.1.val, p.2.2.val]

def latticeVector (n : Translation) : RawCell :=
  ![20 * n 0 + 10 * (n 1 + n 2), 10 * n 1, 10 * n 2]

def reconstruct (p : Cell) (n : Translation) : RawCell :=
  representative p + latticeVector n

private def modFin (a : ℤ) (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨(a % n).toNat, by
    have h0 := Int.emod_nonneg a (by omega : (n : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos a (by omega : (0 : ℤ) < n)
    omega⟩

private theorem modFin_val (a : ℤ) (n : ℕ) (hn : 0 < n) :
    ((modFin a n hn).val : ℤ) = a % n := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg a (by omega))

def reduceCell (r : RawCell) : Cell :=
  (modFin (r 0 - 10 * (r 1 / 10 + r 2 / 10)) 20 (by decide),
    modFin (r 1) 10 (by decide), modFin (r 2) 10 (by decide))

def reduceTranslation (r : RawCell) : Translation :=
  ![(r 0 - 10 * (r 1 / 10 + r 2 / 10)) / 20, r 1 / 10, r 2 / 10]

theorem reconstruct_reduce (r : RawCell) :
    reconstruct (reduceCell r) (reduceTranslation r) = r := by
  funext j
  fin_cases j <;>
    simp [reconstruct, representative, latticeVector, reduceCell, reduceTranslation,
      modFin_val] <;> omega

theorem reduceCell_reconstruct (p : Cell) (n : Translation) :
    reduceCell (reconstruct p n) = p := by
  have hx := p.1.isLt
  have hy := p.2.1.isLt
  have hz := p.2.2.isLt
  apply Prod.ext
  · apply Fin.ext
    have hh := modFin_val
      (reconstruct p n 0 - 10 * (reconstruct p n 1 / 10 + reconstruct p n 2 / 10))
      20 (by decide)
    dsimp [reconstruct, representative, latticeVector] at hh
    change (modFin _ 20 (by decide)).val = _
    dsimp [reconstruct, representative, latticeVector]
    omega
  · apply Prod.ext <;> apply Fin.ext
    · have hh := modFin_val (reconstruct p n 1) 10 (by decide)
      dsimp [reconstruct, representative, latticeVector] at hh
      change (modFin _ 10 (by decide)).val = _
      dsimp [reconstruct, representative, latticeVector]
      omega
    · have hh := modFin_val (reconstruct p n 2) 10 (by decide)
      dsimp [reconstruct, representative, latticeVector] at hh
      change (modFin _ 10 (by decide)).val = _
      dsimp [reconstruct, representative, latticeVector]
      omega

theorem reduceTranslation_reconstruct (p : Cell) (n : Translation) :
    reduceTranslation (reconstruct p n) = n := by
  have hx := p.1.isLt
  have hy := p.2.1.isLt
  have hz := p.2.2.isLt
  funext j
  fin_cases j <;>
    simp [reduceTranslation, reconstruct, representative, latticeVector] <;> omega

def coordinateEquiv : RawCell ≃ Cell × Translation where
  toFun r := (reduceCell r, reduceTranslation r)
  invFun p := reconstruct p.1 p.2
  left_inv := reconstruct_reduce
  right_inv p := by
    exact Prod.ext (reduceCell_reconstruct p.1 p.2) (reduceTranslation_reconstruct p.1 p.2)

theorem latticeVector_add (n t : Translation) :
    latticeVector (n + t) = latticeVector n + latticeVector t := by
  funext j
  fin_cases j <;> simp [latticeVector] <;> ring

theorem reconstruct_add (p : Cell) (n t : Translation) :
    reconstruct p (n + t) = reconstruct p n + latticeVector t := by
  rw [reconstruct, latticeVector_add]
  exact (add_assoc _ _ _).symm

theorem reduceCell_translate (r : RawCell) (n : Translation) :
    reduceCell (r + latticeVector n) = reduceCell r := by
  conv_lhs => rw [← reconstruct_reduce r, ← reconstruct_add]
  exact reduceCell_reconstruct _ _

theorem reduceTranslation_translate (r : RawCell) (n : Translation) :
    reduceTranslation (r + latticeVector n) = reduceTranslation r + n := by
  conv_lhs => rw [← reconstruct_reduce r, ← reconstruct_add]
  exact reduceTranslation_reconstruct _ _

theorem reduceCell_add_representative (r s : RawCell) :
    reduceCell (representative (reduceCell r) + s) = reduceCell (r + s) := by
  have hr : r + s = (representative (reduceCell r) + s) +
      latticeVector (reduceTranslation r) := by
    conv_lhs => rw [← reconstruct_reduce r]
    simp only [reconstruct]
    abel
  rw [hr, reduceCell_translate]

theorem reduceCell_representative (p : Cell) : reduceCell (representative p) = p := by
  have hr : representative p = reconstruct p 0 := by
    funext j
    fin_cases j <;> simp [reconstruct, latticeVector, representative]
  rw [hr, reduceCell_reconstruct]

theorem cell_count : Fintype.card Cell = 2000 := by
  norm_num [Cell]

theorem electric_count : Fintype.card Electric = 6000 := by
  norm_num [Electric, Direction, Cell]

def rawUnit (j : Direction) : RawCell := Pi.single j 1

def forwardRaw (j : Direction) (p : Cell) : RawCell := representative p + rawUnit j

def forwardCell (j : Direction) (p : Cell) : Cell := reduceCell (forwardRaw j p)

def backwardCell (j : Direction) (p : Cell) : Cell :=
  reduceCell (representative p - rawUnit j)

theorem backward_forward (j : Direction) (p : Cell) :
    backwardCell j (forwardCell j p) = p := by
  unfold backwardCell forwardCell forwardRaw
  rw [sub_eq_add_neg, reduceCell_add_representative]
  simp only [add_neg_cancel_right, reduceCell_representative]

theorem forward_backward (j : Direction) (p : Cell) :
    forwardCell j (backwardCell j p) = p := by
  unfold backwardCell forwardCell forwardRaw
  rw [reduceCell_add_representative]
  simp only [sub_add_cancel, reduceCell_representative]

def forwardEquiv (j : Direction) : Cell ≃ Cell where
  toFun := forwardCell j
  invFun := backwardCell j
  left_inv := backward_forward j
  right_inv := forward_backward j

theorem forwardCell_injective (j : Direction) : Function.Injective (forwardCell j) :=
  (forwardEquiv j).injective

theorem forwardCell_bijective (j : Direction) : Function.Bijective (forwardCell j) :=
  (forwardEquiv j).bijective

noncomputable section

def character (k : Momentum) (n : Translation) : ℂ :=
  Complex.exp (Complex.I * ((∑ j : Direction, k j * (n j : ℝ)) : ℂ))

theorem character_zero (k : Momentum) : character k 0 = 1 := by
  simp [character]

theorem character_add (k : Momentum) (n t : Translation) :
    character k (n + t) = character k n * character k t := by
  simp only [character, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib,
    Complex.ofReal_add, Complex.exp_add]

theorem character_conj (k : Momentum) (n : Translation) :
    star (character k n) = character k (-n) := by
  simp only [character, Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib,
    Complex.ofReal_neg, mul_neg]
  change starRingEnd ℂ (Complex.exp _) = _
  rw [← Complex.exp_conj]
  simp

theorem character_unit (k : Momentum) (n : Translation) :
    star (character k n) * character k n = 1 := by
  rw [character_conj, ← character_add, neg_add_cancel, character_zero]

def timeReversalMomentum (k : Translation) : Momentum := fun j => Real.pi * k j

theorem character_timeReversal (k n : Translation) :
    character (timeReversalMomentum k) n = (-1 : ℂ) ^ (∑ j, k j * n j) := by
  unfold character timeReversalMomentum
  have he : Complex.I * ((∑ j : Direction, Real.pi * (k j : ℝ) * (n j : ℝ)) : ℂ) =
      ((∑ j : Direction, k j * n j : ℤ) : ℂ) * (Real.pi * Complex.I) := by
    simp only [Fin.sum_univ_three]
    push_cast
    ring
  simp only [Complex.ofReal_mul] at *
  rw [he, Complex.exp_int_mul, Complex.exp_pi_mul_I]

def extend (k : Momentum) (v : Cell → ℂ) (r : RawCell) : ℂ :=
  character k (reduceTranslation r) * v (reduceCell r)

theorem extend_translate (k : Momentum) (v : Cell → ℂ) (r : RawCell)
    (n : Translation) :
    extend k v (r + latticeVector n) = character k n * extend k v r := by
  rw [extend, reduceTranslation_translate, reduceCell_translate, character_add, extend]
  ring

theorem extend_representative (k : Momentum) (v : Cell → ℂ) (p : Cell) :
    extend k v (representative p) = v p := by
  have hr : representative p = reconstruct p 0 := by
    funext j
    fin_cases j <;> simp [reconstruct, latticeVector, representative]
  rw [hr, extend, reduceCell_reconstruct, reduceTranslation_reconstruct, character_zero, one_mul]

def boundaryPhase (k : Momentum) (j : Direction) (p : Cell) : ℂ :=
  character k (reduceTranslation (forwardRaw j p))

def shift (k : Momentum) (j : Direction) : Matrix Cell Cell ℂ :=
  fun p q => if q = forwardCell j p then boundaryPhase k j p else 0

theorem shift_mul_conjTranspose (k : Momentum) (j : Direction) :
    shift k j * (shift k j).conjTranspose = 1 := by
  ext p q
  by_cases hpq : p = q
  · subst q
    have hu : boundaryPhase k j p * star (boundaryPhase k j p) = 1 := by
      rw [mul_comm]
      exact character_unit k _
    simpa [shift, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_mul] using hu
  · have hf : forwardCell j p ≠ forwardCell j q := fun h => hpq (forwardCell_injective j h)
    simp [shift, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_mul, hf, hpq]

theorem shift_conjTranspose_mul (k : Momentum) (j : Direction) :
    (shift k j).conjTranspose * shift k j = 1 := by
  exact mul_eq_one_comm.mp (shift_mul_conjTranspose k j)

def difference (k : Momentum) (j : Direction) : Matrix Cell Cell ℂ :=
  fun p q => (if q = forwardCell j p then boundaryPhase k j p else 0) -
    (if q = p then 1 else 0)

theorem difference_eq_shift_sub_one (k : Momentum) (j : Direction) :
    difference k j = shift k j - 1 := by
  ext p q
  simp [difference, shift, Matrix.one_apply, eq_comm]

theorem difference_mulVec (k : Momentum) (j : Direction) (v : Cell → ℂ) (p : Cell) :
    (difference k j *ᵥ v) p = boundaryPhase k j p * v (forwardCell j p) - v p := by
  simp [difference, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul]

theorem extend_difference (k : Momentum) (j : Direction) (v : Cell → ℂ) (r : RawCell) :
    extend k (difference k j *ᵥ v) r =
      extend k v (r + rawUnit j) - extend k v r := by
  let p := reduceCell r
  let n := reduceTranslation r
  have hr : r = reconstruct p n := (reconstruct_reduce r).symm
  have hs : reconstruct p n + rawUnit j = forwardRaw j p + latticeVector n := by
    simp only [reconstruct, forwardRaw]
    abel
  rw [hr, hs, extend_translate]
  simp only [extend, reduceCell_reconstruct, reduceTranslation_reconstruct, difference_mulVec]
  change character k n * (boundaryPhase k j p * v (forwardCell j p) - v p) =
    character k n * (boundaryPhase k j p * v (forwardCell j p)) - character k n * v p
  ring

def curl (k : Momentum) : Matrix Face Electric ℂ := fun i j =>
  if i.1 = 0 then
    if j.1 = 2 then difference k 1 i.2 j.2
    else if j.1 = 1 then -difference k 2 i.2 j.2 else 0
  else if i.1 = 1 then
    if j.1 = 0 then difference k 2 i.2 j.2
    else if j.1 = 2 then -difference k 0 i.2 j.2 else 0
  else
    if j.1 = 1 then difference k 0 i.2 j.2
    else if j.1 = 0 then -difference k 1 i.2 j.2 else 0

theorem curl_mulVec (k : Momentum) (v : Electric → ℂ) (d : Direction) (p : Cell) :
    (curl k *ᵥ v) (d, p) =
      if d = 0 then
        (difference k 1 *ᵥ fun q => v (2, q)) p -
          (difference k 2 *ᵥ fun q => v (1, q)) p
      else if d = 1 then
        (difference k 2 *ᵥ fun q => v (0, q)) p -
          (difference k 0 *ᵥ fun q => v (2, q)) p
      else
        (difference k 0 *ᵥ fun q => v (1, q)) p -
          (difference k 1 *ᵥ fun q => v (0, q)) p := by
  fin_cases d <;>
    simp [curl, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three,
      neg_mul, Finset.sum_neg_distrib] <;> ring

theorem curl_adjoint_mulVec (k : Momentum) (v : Face → ℂ) (d : Direction) (p : Cell) :
    ((curl k).conjTranspose *ᵥ v) (d, p) =
      if d = 0 then
        ((difference k 2).conjTranspose *ᵥ fun q => v (1, q)) p -
          ((difference k 1).conjTranspose *ᵥ fun q => v (2, q)) p
      else if d = 1 then
        ((difference k 0).conjTranspose *ᵥ fun q => v (2, q)) p -
          ((difference k 2).conjTranspose *ᵥ fun q => v (0, q)) p
      else
        ((difference k 1).conjTranspose *ᵥ fun q => v (0, q)) p -
          ((difference k 0).conjTranspose *ᵥ fun q => v (1, q)) p := by
  fin_cases d <;>
    simp [curl, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, neg_mul, Finset.sum_neg_distrib] <;> ring

def conventionalCell (r : RawCell) : Cell20 := fun j => (r j : ZMod 20)

theorem conventionalCell_add (r s : RawCell) :
    conventionalCell (r + s) = conventionalCell r + conventionalCell s := by
  funext j
  simp [conventionalCell]

theorem conventionalCell_sub (r s : RawCell) :
    conventionalCell (r - s) = conventionalCell r - conventionalCell s := by
  funext j
  simp [conventionalCell]

theorem conventionalCell_rawUnit (j : Direction) :
    conventionalCell (rawUnit j) = unitCell j := by
  funext i
  by_cases h : i = j <;> simp [conventionalCell, rawUnit, unitCell, h]

def edgeAverage (material : Cell20 → ℝ) (e : Electric) : ℝ :=
  let p := transverseDirections e.1
  let r := representative e.2
  (material (conventionalCell r) + material (conventionalCell (r - rawUnit p.1)) +
    material (conventionalCell (r - rawUnit p.2)) +
    material (conventionalCell (r - rawUnit p.1 - rawUnit p.2))) / 4

theorem edgeAverage_binding (material : Cell20 → ℝ) (e : Electric) :
    edgeAverage material e =
      PeriodicYee.edgeAverage material (e.1, conventionalCell (representative e.2)) := by
  simp [edgeAverage, PeriodicYee.edgeAverage, conventionalCell_sub, conventionalCell_rawUnit]

def mass (material : Cell20 → ℝ) : Matrix Electric Electric ℂ :=
  Matrix.diagonal fun e => (edgeAverage material e : ℂ)

def fiber (material : Cell20 → ℝ) (k : Momentum) : Matrix Electric Electric ℂ :=
  (curl k).conjTranspose * curl k - (1 / 64 : ℂ) • mass material

theorem mass_hermitian (material : Cell20 → ℝ) : (mass material).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  change star (fun e : Electric => (edgeAverage material e : ℂ)) = _
  funext e
  simp

theorem fiber_hermitian (material : Cell20 → ℝ) (k : Momentum) :
    (fiber material k).IsHermitian := by
  apply (Matrix.isHermitian_conjTranspose_mul_self (curl k)).sub
  exact (mass_hermitian material).smul (by
    change star (1 / 64 : ℂ) = _
    simp)

end
end Maxwell.Spectral.PrimitiveYee
