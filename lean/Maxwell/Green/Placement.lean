import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Integer placement matrices constructed by rounding a scaled real matrix. -/

noncomputable section

namespace Maxwell.Green

open Matrix
open scoped Matrix Matrix.Norms.L2Operator

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

abbrev matrixAction (A : Mat3) : Vec3 →L[ℝ] Vec3 :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A

/-- The placement matrix is an actual integer matrix, obtained entrywise. -/
def roundedPlacement (M : ℕ) (Q : Mat3) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => ⌊(M : ℝ) * Q i j⌋

/-- The real-linear action of the integer placement matrix. -/
def roundedPlacementReal (M : ℕ) (Q : Mat3) : Mat3 :=
  fun i j => (roundedPlacement M Q i j : ℝ)

theorem roundedPlacement_entry_error (M : ℕ) (Q : Mat3) (i j : Fin 3) :
    |roundedPlacementReal M Q i j - (M : ℝ) * Q i j| < 1 := by
  change |(⌊(M : ℝ) * Q i j⌋ : ℝ) - (M : ℝ) * Q i j| < 1
  rw [abs_lt]
  constructor
  · linarith [Int.lt_floor_add_one ((M : ℝ) * Q i j)]
  · linarith [Int.floor_le ((M : ℝ) * Q i j)]

/-- Entrywise error at most one gives Euclidean operator error at most three.
The constant is the square root of the number of entries. -/
theorem matrix_opNorm_le_three (A : Mat3) (hA : ∀ i j, |A i j| ≤ 1) : ‖A‖ ≤ 3 := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine (matrixAction A).opNorm_le_bound (by norm_num) fun x => ?_
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hrow : ∀ i, (∑ j : Fin 3, A i j * x j) ^ 2 ≤
      3 * ∑ j : Fin 3, (x j) ^ 2 := by
    intro i
    have hs : ∑ j : Fin 3, (A i j) ^ 2 ≤ (3 : ℝ) := by
      calc
        ∑ j : Fin 3, (A i j) ^ 2 ≤ ∑ _j : Fin 3, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          have ha := hA i j
          have hab := (abs_le.mp ha)
          nlinarith
        _ = 3 := by norm_num
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j)
      (fun j => x j)
    exact hcs.trans (mul_le_mul_of_nonneg_right hs (Finset.sum_nonneg (by intros; positivity)))
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Real.norm_eq_abs,
    sq_abs]
  calc
    ∑ i : Fin 3, (∑ j : Fin 3, A i j * x j) ^ 2 ≤
        ∑ _i : Fin 3, 3 * ∑ j : Fin 3, (x j) ^ 2 :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = (3 * ‖x‖) ^ 2 := by
      simp [mul_pow, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
      ring

theorem roundedPlacement_opNorm_error (M : ℕ) (Q : Mat3) :
    ‖roundedPlacementReal M Q - (M : ℝ) • Q‖ ≤ 3 := by
  apply matrix_opNorm_le_three
  intro i j
  exact (roundedPlacement_entry_error M Q i j).le

/-- Applying a fixed inverse metric multiplies the rounding error by at most
its Euclidean operator norm. -/
theorem roundedPlacement_metric_error (M : ℕ) (Q P : Mat3) (x : Vec3) :
    ‖matrixAction (P * (roundedPlacementReal M Q - (M : ℝ) • Q)) x‖ ≤
      3 * ‖P‖ * ‖x‖ := by
  calc
    _ ≤ ‖P * (roundedPlacementReal M Q - (M : ℝ) • Q)‖ * ‖x‖ :=
      (matrixAction _).le_opNorm x
    _ ≤ (‖P‖ * ‖roundedPlacementReal M Q - (M : ℝ) • Q‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg x)
    _ ≤ (‖P‖ * 3) * ‖x‖ := by gcongr; exact roundedPlacement_opNorm_error M Q
    _ = 3 * ‖P‖ * ‖x‖ := by ring

/-- In the inverse metric, the rounded placement is the dilation by `M` plus
the controlled rounding error. -/
theorem roundedPlacement_metric_decomposition (M : ℕ) (Q P : Mat3)
    (hPQ : P * Q = 1) (x : Vec3) :
    matrixAction (P * roundedPlacementReal M Q) x - (M : ℝ) • x =
      matrixAction (P * (roundedPlacementReal M Q - (M : ℝ) • Q)) x := by
  simp [matrixAction, Matrix.mul_sub, hPQ]

/-- Both Euclidean metric distortion bounds follow from the actual rounded
matrix, with its absolute error displayed explicitly. -/
theorem roundedPlacement_distortion (M : ℕ) (Q P : Mat3)
    (hPQ : P * Q = 1) (x : Vec3) :
    ((M : ℝ) - 3 * ‖P‖) * ‖x‖ ≤ ‖matrixAction (P * roundedPlacementReal M Q) x‖ ∧
      ‖matrixAction (P * roundedPlacementReal M Q) x‖ ≤
        ((M : ℝ) + 3 * ‖P‖) * ‖x‖ := by
  have he := roundedPlacement_metric_error M Q P x
  rw [← roundedPlacement_metric_decomposition M Q P hPQ x] at he
  have hn := abs_norm_sub_norm_le
    (matrixAction (P * roundedPlacementReal M Q) x) ((M : ℝ) • x)
  have hmabs : |(M : ℝ)| = (M : ℝ) := abs_of_nonneg (Nat.cast_nonneg M)
  rw [norm_smul, Real.norm_eq_abs, hmabs] at hn
  have h := abs_le.mp (hn.trans he)
  constructor <;> nlinarith [h.1, h.2]

/-- A prescribed relative distortion follows by choosing the scale larger
than the absolute rounding error divided by that tolerance. -/
theorem roundedPlacement_relative_distortion (M : ℕ) (Q P : Mat3)
    (hPQ : P * Q = 1) (η : ℝ) (hM : 3 * ‖P‖ ≤ η * (M : ℝ)) (x : Vec3) :
    (M : ℝ) * (1 - η) * ‖x‖ ≤ ‖matrixAction (P * roundedPlacementReal M Q) x‖ ∧
      ‖matrixAction (P * roundedPlacementReal M Q) x‖ ≤
        (M : ℝ) * (1 + η) * ‖x‖ := by
  obtain ⟨hl, hu⟩ := roundedPlacement_distortion M Q P hPQ x
  have hMx := mul_le_mul_of_nonneg_right hM (norm_nonneg x)
  constructor <;> nlinarith

theorem roundedPlacement_injective (M : ℕ) (Q P : Mat3)
    (hPQ : P * Q = 1) (hM : 3 * ‖P‖ < (M : ℝ)) :
    Function.Injective (matrixAction (roundedPlacementReal M Q)) := by
  intro x y hxy
  have hzero : matrixAction (P * roundedPlacementReal M Q) (x - y) = 0 := by
    simp only [matrixAction, map_mul, mul_apply_eq_comp, map_sub]
    exact sub_eq_zero.mpr (congrArg (matrixAction P) hxy)
  have hl := (roundedPlacement_distortion M Q P hPQ (x - y)).1
  rw [hzero, norm_zero] at hl
  have hz : ‖x - y‖ = 0 := by
    have hn := norm_nonneg (x - y)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- The rounded integer placement has an invertible real matrix whenever its
scale exceeds the absolute error in the inverse metric. -/
theorem roundedPlacement_isUnit (M : ℕ) (Q P : Mat3)
    (hPQ : P * Q = 1) (hM : 3 * ‖P‖ < (M : ℝ)) :
    IsUnit (roundedPlacementReal M Q) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have h := roundedPlacement_injective M Q P hPQ hM
    (show matrixAction (roundedPlacementReal M Q) (WithLp.toLp 2 x) =
      matrixAction (roundedPlacementReal M Q) (WithLp.toLp 2 y) from
      congrArg (WithLp.toLp 2) hxy)
  exact congrArg WithLp.ofLp h

/-- Archimedeanness supplies a natural-number scale for every positive
distortion tolerance. No placement-existence premise is assumed. -/
theorem exists_roundedPlacement_scale (P : Mat3) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℕ, 0 < M ∧ 3 * ‖P‖ < η * (M : ℝ) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (3 * ‖P‖ / η)
  have hnonneg : 0 ≤ 3 * ‖P‖ / η := by positivity
  have hpos : 0 < (M : ℝ) := hnonneg.trans_lt hM
  refine ⟨M, by exact_mod_cast hpos, ?_⟩
  have hm := (div_lt_iff₀ hη).mp hM
  nlinarith

/-- Complete integer-placement existence: for every requested distortion
between zero and one, an explicit floor-rounded integer matrix is invertible
and has the two required metric bounds. -/
theorem exists_integer_placement (Q P : Mat3) (hPQ : P * Q = 1)
    (η : ℝ) (hη₀ : 0 < η) (hη₁ : η < 1) :
    ∃ M : ℕ, 0 < M ∧ IsUnit (roundedPlacementReal M Q) ∧
      ∀ x : Vec3,
        (M : ℝ) * (1 - η) * ‖x‖ ≤ ‖matrixAction (P * roundedPlacementReal M Q) x‖ ∧
        ‖matrixAction (P * roundedPlacementReal M Q) x‖ ≤
          (M : ℝ) * (1 + η) * ‖x‖ := by
  obtain ⟨M, hM₀, hMη⟩ := exists_roundedPlacement_scale P η hη₀
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM₀
  have hM : 3 * ‖P‖ < (M : ℝ) := by nlinarith
  exact ⟨M, hM₀, roundedPlacement_isUnit M Q P hPQ hM,
    roundedPlacement_relative_distortion M Q P hPQ η hMη.le⟩

end Maxwell.Green
