import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact containing-box counts for a fixed integer placement matrix. -/

namespace Maxwell.Green

open Matrix
open scoped Matrix

/-- Absolute row sum, in natural numbers so that it directly bounds integer
box dimensions. -/
def rowSumAbs (B : Matrix (Fin 3) (Fin 3) ℤ) (i : Fin 3) : ℕ :=
  ∑ j, (B i j).natAbs

/-- The fixed coordinate expansion factor of a placement matrix. -/
def placementBoxFactor (B : Matrix (Fin 3) (Fin 3) ℤ) : ℕ :=
  Finset.univ.sup (rowSumAbs B)

theorem rowSumAbs_le_placementBoxFactor (B : Matrix (Fin 3) (Fin 3) ℤ) (i : Fin 3) :
    rowSumAbs B i ≤ placementBoxFactor B :=
  Finset.le_sup (Finset.mem_univ i)

/-- Matrix multiplication sends a coordinate-bounded integer vector into the
box determined by the absolute row sums. -/
theorem placement_coordinate_bound (B : Matrix (Fin 3) (Fin 3) ℤ)
    (z : Fin 3 → ℤ) (L : ℕ) (hz : ∀ j, |z j| ≤ (L : ℤ)) (i : Fin 3) :
    |(B *ᵥ z) i| ≤ (rowSumAbs B i : ℤ) * (L : ℤ) := by
  calc
    |(B *ᵥ z) i| = |∑ j, B i j * z j| := rfl
    _ ≤ ∑ j, |B i j * z j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |B i j| * |z j| := by simp only [abs_mul]
    _ ≤ ∑ j, |B i j| * (L : ℤ) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hz j) (abs_nonneg _))
    _ = (rowSumAbs B i : ℤ) * (L : ℤ) := by
      simp only [rowSumAbs, Nat.cast_sum, Int.natCast_natAbs, Finset.sum_mul]

theorem placement_uniform_coordinate_bound (B : Matrix (Fin 3) (Fin 3) ℤ)
    (z : Fin 3 → ℤ) (L : ℕ) (hz : ∀ j, |z j| ≤ (L : ℤ)) (i : Fin 3) :
    |(B *ᵥ z) i| ≤ ((placementBoxFactor B * L : ℕ) : ℤ) := by
  have hC : (rowSumAbs B i : ℤ) ≤ (placementBoxFactor B : ℤ) := by
    exact_mod_cast rowSumAbs_le_placementBoxFactor B i
  simpa only [Nat.cast_mul] using (placement_coordinate_bound B z L hz i).trans
    (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg L))

/-- All integer sites in the closed cube with half-side `L`. -/
def integerCube (L : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(L : ℤ)) (L : ℤ)

theorem mem_integerCube (L : ℕ) (z : Fin 3 → ℤ) :
    z ∈ integerCube L ↔ ∀ i, |z i| ≤ (L : ℤ) := by
  simp only [integerCube, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

/-- The count includes every site of the containing cube, including empty
regions between placed structures. -/
theorem card_integerCube (L : ℕ) : (integerCube L).card = (2 * L + 1) ^ 3 := by
  rw [integerCube, Fintype.card_piFinset_const, Int.card_Icc]
  congr 1
  have h : (L : ℤ) + 1 - -(L : ℤ) = ((2 * L + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h, Int.toNat_natCast]

/-- A side of the physical containing box has exactly `2 C L + 1` lattice
sites; `C` depends only on the fixed integer placement matrix. -/
theorem placement_containing_side_count (B : Matrix (Fin 3) (Fin 3) ℤ) (L : ℕ) :
    (Finset.Icc (-((placementBoxFactor B * L : ℕ) : ℤ))
      ((placementBoxFactor B * L : ℕ) : ℤ)).card = 2 * placementBoxFactor B * L + 1 := by
  rw [Int.card_Icc]
  have h : ((placementBoxFactor B * L : ℕ) : ℤ) + 1 -
      -((placementBoxFactor B * L : ℕ) : ℤ) =
      ((2 * placementBoxFactor B * L + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h, Int.toNat_natCast]

theorem placement_cube_image_subset (B : Matrix (Fin 3) (Fin 3) ℤ) (L : ℕ) :
    (integerCube L).image (B *ᵥ ·) ⊆ integerCube (placementBoxFactor B * L) := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  apply (mem_integerCube _ _).2
  exact placement_uniform_coordinate_bound B w L ((mem_integerCube _ _).1 hw)

theorem placement_cube_image_card_le (B : Matrix (Fin 3) (Fin 3) ℤ) (L : ℕ) :
    ((integerCube L).image (B *ᵥ ·)).card ≤ (2 * placementBoxFactor B * L + 1) ^ 3 := by
  have h := Finset.card_le_card (placement_cube_image_subset B L)
  simpa only [card_integerCube, Nat.mul_assoc] using h

/-- Substitution of spacing, balanced logical half-side, and buffer in the
exact full-box volume formula. -/
theorem placement_buffered_cube_count (B : Matrix (Fin 3) (Fin 3) ℤ)
    (spacing logicalSide buffer : ℕ) :
    (integerCube (placementBoxFactor B * (spacing * logicalSide + buffer))).card =
      (2 * placementBoxFactor B * spacing * logicalSide +
        2 * placementBoxFactor B * buffer + 1) ^ 3 := by
  rw [card_integerCube]
  congr 1
  ring

/-- When the collar is added in physical coordinates after placement, its
width is added after the fixed matrix expansion factor. -/
theorem placement_spacing_buffer_coordinate_bound
    (B : Matrix (Fin 3) (Fin 3) ℤ) (z q : Fin 3 → ℤ)
    (spacing logicalSide buffer : ℕ)
    (hz : ∀ j, |z j| ≤ (logicalSide : ℤ))
    (hq : ∀ j, |q j| ≤ (buffer : ℤ)) (i : Fin 3) :
    |(spacing : ℤ) * (B *ᵥ z) i + q i| ≤
      ((spacing * placementBoxFactor B * logicalSide + buffer : ℕ) : ℤ) := by
  have hB := placement_uniform_coordinate_bound B z logicalSide hz i
  have hd : |(spacing : ℤ)| = (spacing : ℤ) := abs_of_nonneg (Nat.cast_nonneg _)
  calc
    _ ≤ |(spacing : ℤ) * (B *ᵥ z) i| + |q i| := abs_add_le _ _
    _ = (spacing : ℤ) * |(B *ᵥ z) i| + |q i| := by rw [abs_mul, hd]
    _ ≤ (spacing : ℤ) * ((placementBoxFactor B * logicalSide : ℕ) : ℤ) +
        (buffer : ℤ) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _)) (hq i)
    _ = _ := by push_cast; ring

theorem placement_spacing_buffer_mem_cube
    (B : Matrix (Fin 3) (Fin 3) ℤ) (z q : Fin 3 → ℤ)
    (spacing logicalSide buffer : ℕ)
    (hz : z ∈ integerCube logicalSide) (hq : q ∈ integerCube buffer) :
    (fun i => (spacing : ℤ) * (B *ᵥ z) i + q i) ∈
      integerCube (spacing * placementBoxFactor B * logicalSide + buffer) := by
  apply (mem_integerCube _ _).2
  exact placement_spacing_buffer_coordinate_bound B z q spacing logicalSide buffer
    ((mem_integerCube _ _).1 hz) ((mem_integerCube _ _).1 hq)

/-- Exact full physical containing-box count with spacing and a physical
collar, rather than merely the number of occupied sites. -/
theorem placement_spacing_buffer_cube_count (B : Matrix (Fin 3) (Fin 3) ℤ)
    (spacing logicalSide buffer : ℕ) :
    (integerCube (spacing * placementBoxFactor B * logicalSide + buffer)).card =
      (2 * spacing * placementBoxFactor B * logicalSide + 2 * buffer + 1) ^ 3 := by
  rw [card_integerCube]
  congr 1
  ring

end Maxwell.Green
