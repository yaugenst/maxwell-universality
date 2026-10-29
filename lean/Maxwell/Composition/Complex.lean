import Maxwell.Target
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-! Every complex field is reduced to its real part using the actual
Euclidean norm and the actual rational Maxwell matrix from `Target`.
There is no restriction to a preferred solver output. -/

namespace Maxwell.Composition

section FiniteRealPart

variable {ι : Type*}

def euclideanRealPart (y : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => (y i).re

def euclideanComplexLift (x : EuclideanSpace ℝ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun i => (x i : ℂ)

@[simp] theorem euclideanRealPart_apply (y : EuclideanSpace ℂ ι) (i : ι) :
    euclideanRealPart y i = (y i).re := rfl

@[simp] theorem euclideanComplexLift_apply (x : EuclideanSpace ℝ ι) (i : ι) :
    euclideanComplexLift x i = (x i : ℂ) := rfl

@[simp] theorem euclideanRealPart_sub (x y : EuclideanSpace ℂ ι) :
    euclideanRealPart (x - y) = euclideanRealPart x - euclideanRealPart y := by
  ext i
  simp [euclideanRealPart]

@[simp] theorem euclideanRealPart_lift (x : EuclideanSpace ℝ ι) :
    euclideanRealPart (euclideanComplexLift x) = x := by
  ext i
  simp

variable [Fintype ι]

theorem euclideanRealPart_norm_le (y : EuclideanSpace ℂ ι) :
    ‖euclideanRealPart y‖ ≤ ‖y‖ := by
  have hsquare : ‖euclideanRealPart y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    have h := Complex.abs_re_le_norm (y i)
    simpa only [euclideanRealPart_apply, Real.norm_eq_abs, pow_two] using
      mul_self_le_mul_self (abs_nonneg (y i).re) h
  nlinarith only [hsquare, norm_nonneg (euclideanRealPart y), norm_nonneg y]

@[simp] theorem euclideanComplexLift_norm (x : EuclideanSpace ℝ ι) :
    ‖euclideanComplexLift x‖ = ‖x‖ := by
  have hsquare : ‖euclideanComplexLift x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq]
  nlinarith only [hsquare, norm_nonneg (euclideanComplexLift x), norm_nonneg x]

theorem realPart_matrix_action [DecidableEq ι]
    (A : Matrix ι ι ℝ) (y : EuclideanSpace ℂ ι) :
    euclideanRealPart (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)
      (A.map fun a => (a : ℂ)) y) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) A (euclideanRealPart y) := by
  ext i
  change ((∑ j, (A i j : ℂ) * y j)).re = ∑ j, A i j * (y j).re
  simp

/-- Real matrices and real sources cannot increase a residual when a
complex solver output is replaced by its real part. -/
theorem realPart_matrix_residual_norm_le [DecidableEq ι]
    (A : Matrix ι ι ℝ) (f : EuclideanSpace ℝ ι) (y : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) A (euclideanRealPart y) - f‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (A.map fun a => (a : ℂ)) y -
        euclideanComplexLift f‖ := by
  have h := euclideanRealPart_norm_le
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (A.map fun a => (a : ℂ)) y -
      euclideanComplexLift f)
  simpa only [euclideanRealPart_sub, euclideanRealPart_lift,
    realPart_matrix_action] using h

end FiniteRealPart

/-- This specialization uses the finite target's actual emitted rational
material/source arrays and its stated admissibility predicate. -/
theorem target_admissible_real_residual {n : ℕ} (I : Target.Instance n)
    (y : EuclideanSpace ℂ I.box.Edge) (hy : I.Admissible y) :
    ‖I.realOperator (euclideanRealPart y) -
        WithLp.toLp 2 (fun e => (I.source e : ℝ))‖ ≤
      (I.tolerance : ℝ) * ‖WithLp.toLp 2 (fun e => (I.source e : ℝ))‖ := by
  let f : EuclideanSpace ℝ I.box.Edge := WithLp.toLp 2 fun e => (I.source e : ℝ)
  have hMatrix : I.complexMatrix = I.realMatrix.map (fun a => (a : ℂ)) := by
    ext i j
    simp [Target.Instance.complexMatrix, Target.Instance.realMatrix]
  have hSource : I.complexSource = euclideanComplexLift f := by
    ext i
    simp [Target.Instance.complexSource, f]
  have h := realPart_matrix_residual_norm_le I.realMatrix f y
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := I.box.Edge) I.realMatrix
    (euclideanRealPart y) - f‖ ≤ (I.tolerance : ℝ) * ‖f‖
  apply h.trans
  simpa only [Target.Instance.Admissible, Target.Instance.complexOperator,
    hMatrix, hSource, euclideanComplexLift_norm] using hy

end Maxwell.Composition
