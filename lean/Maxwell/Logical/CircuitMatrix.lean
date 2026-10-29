import Maxwell.Logical.Circuit
import Maxwell.Logical.Path
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Matrix semantics of the actual finite acyclic interpreter.
Both inverses below are constructed by forward recursion. No matrix inverse
or existence premise is assumed.
-/

namespace Maxwell.Logical.Circuit

open Matrix
open scoped Matrix
open scoped Matrix.Norms.L2Operator

def errorMap {n d : ℕ} (c : Circuit n d) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun := c.evaluate 0
  map_add' r s := by simpa using c.evaluate_add 0 0 r s
  map_smul' t r := by simpa using c.evaluate_smul t 0 r

theorem evaluate_injective {n d : ℕ} (c : Circuit n d) (input : Fin n → ℝ) :
    Function.Injective (c.evaluate input) :=
  Function.LeftInverse.injective (c.residual_evaluate input)

def equationMap {n d : ℕ} (c : Circuit n d) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun := c.residual 0
  map_add' r s := by
    apply c.evaluate_injective 0
    rw [c.evaluate_residual]
    have h := c.evaluate_add 0 0 (c.residual 0 r) (c.residual 0 s)
    simpa [c.evaluate_residual] using h.symm
  map_smul' t r := by
    apply c.evaluate_injective 0
    rw [c.evaluate_residual]
    have h := c.evaluate_smul t 0 (c.residual 0 r)
    simpa [c.evaluate_residual] using h.symm

/-- The actual unit-lower-triangular equation matrix. -/
def equationMatrix {n d : ℕ} (c : Circuit n d) : Matrix (Fin d) (Fin d) ℝ :=
  c.equationMap.toMatrix'

/-- The inverse obtained from the finite acyclic recurrence. -/
def errorMatrix {n d : ℕ} (c : Circuit n d) : Matrix (Fin d) (Fin d) ℝ :=
  c.errorMap.toMatrix'

@[simp] theorem errorMatrix_mulVec {n d : ℕ} (c : Circuit n d) (r : Fin d → ℝ) :
    c.errorMatrix *ᵥ r = c.evaluate 0 r :=
  LinearMap.toMatrix'_mulVec c.errorMap r

@[simp] theorem equationMatrix_mulVec {n d : ℕ} (c : Circuit n d) (r : Fin d → ℝ) :
    c.equationMatrix *ᵥ r = c.residual 0 r :=
  LinearMap.toMatrix'_mulVec c.equationMap r

theorem equationMatrix_mul_errorMatrix {n d : ℕ} (c : Circuit n d) :
    c.equationMatrix * c.errorMatrix = 1 := by
  change c.equationMap.toMatrix' * c.errorMap.toMatrix' = 1
  rw [← LinearMap.toMatrix'_comp]
  have h : c.equationMap.comp c.errorMap = LinearMap.id := by
    apply LinearMap.ext
    intro r
    exact c.residual_evaluate 0 r
  rw [h, LinearMap.toMatrix'_id]

theorem errorMatrix_mul_equationMatrix {n d : ℕ} (c : Circuit n d) :
    c.errorMatrix * c.equationMatrix = 1 := by
  change c.errorMap.toMatrix' * c.equationMap.toMatrix' = 1
  rw [← LinearMap.toMatrix'_comp]
  have h : c.errorMap.comp c.equationMap = LinearMap.id := by
    apply LinearMap.ext
    intro r
    exact c.evaluate_residual 0 r
  rw [h, LinearMap.toMatrix'_id]

theorem equationMatrix_nonsing_inv {n d : ℕ} (c : Circuit n d) :
    c.equationMatrix⁻¹ = c.errorMatrix :=
  Matrix.inv_eq_right_inv c.equationMatrix_mul_errorMatrix

/-- Entries are sums of all weighted dependency paths from the specified
equation-error source, computed by the actual interpreter. -/
theorem errorMatrix_entry {n d : ℕ} (c : Circuit n d) (i j : Fin d) :
    c.errorMatrix i j = c.evaluate 0 (Pi.single j 1) i := rfl

theorem errorMatrix_entry_abs_le {n d : ℕ} (c : Circuit n d) (i j : Fin d) :
    |c.errorMatrix i j| ≤ c.absoluteCoefficients.errorMatrix i j := by
  rw [errorMatrix_entry, errorMatrix_entry]
  have h := c.abs_evaluate_le_envelope 0 (Pi.single j 1) i
  have hzero : (fun k : Fin n => |(0 : Fin n → ℝ) k|) = 0 := by ext k; simp
  have hsingle : (fun k : Fin d => |(Pi.single j (1 : ℝ) : Fin d → ℝ) k|) =
      (Pi.single j (1 : ℝ) : Fin d → ℝ) := by
    funext k
    by_cases hkj : k = j
    · subst k; simp
    · simp [hkj]
  rw [hzero, hsingle] at h
  exact h

/-- Entrywise magnitude bounds imply the Euclidean bound used in the circuit
proof. This is a general matrix estimate; the compiler must separately prove
its weighted dependency-path multiplicity bound. -/
theorem norm_le_card_mul_entry_bound {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℝ) (P : ℝ) (hP : 0 ≤ P) (hA : ∀ i j, |A i j| ≤ P) :
    ‖A‖ ≤ Fintype.card d * P := by
  by_cases hz : P = 0
  · subst P
    have hzero : A = 0 := by
      ext i j
      exact abs_eq_zero.mp (le_antisymm (hA i j) (abs_nonneg _))
    simp [hzero]
  · have hp : 0 < P := lt_of_le_of_ne hP (Ne.symm hz)
    have hscaled : ∀ i j, |(P⁻¹ • A) i j| ≤ 1 := by
      intro i j
      simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hp]
      calc
        P⁻¹ * |A i j| ≤ P⁻¹ * P := mul_le_mul_of_nonneg_left (hA i j) (inv_nonneg.mpr hP)
        _ = 1 := inv_mul_cancel₀ hz
    have hbound := Path.entry_bound_euclidean_norm (P⁻¹ • A) hscaled
    have hnorm : ‖P⁻¹ • A‖ = P⁻¹ * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp]
    rw [hnorm] at hbound
    have ht := mul_le_mul_of_nonneg_left hbound hP
    calc
      ‖A‖ = P * (P⁻¹ * ‖A‖) := by field_simp
      _ ≤ P * (Fintype.card d : ℝ) := ht
      _ = _ := mul_comm _ _

/-- The `S^2` Euclidean bound follows from at most `S` unit-weight paths
between any two gates. The path-count premise is explicit, not confused
with a proof that the full sparse compiler has been constructed. -/
theorem inverse_norm_of_path_bound {n d : ℕ} (c : Circuit n d)
    (hpath : ∀ i j, c.absoluteCoefficients.errorMatrix i j ≤ d) :
    ‖c.equationMatrix⁻¹‖ ≤ (d : ℝ) ^ 2 := by
  rw [equationMatrix_nonsing_inv]
  have hentry : ∀ i j, |c.errorMatrix i j| ≤ (d : ℝ) :=
    fun i j => (c.errorMatrix_entry_abs_le i j).trans (hpath i j)
  have h := norm_le_card_mul_entry_bound c.errorMatrix d (by positivity) hentry
  simpa [pow_two] using h

end Maxwell.Logical.Circuit
