import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Executable acyclic linear circuits and arbitrary residuals

Every appended equation refers only to already allocated coordinates.
The recursive interpreter is an actual forward solve of those equations.
The theorems below quantify over errors in every equation and every input
size; there is no premise asserting existence of a logical realization.
-/

namespace Maxwell.Logical

open scoped BigOperators

inductive Circuit (inputs : ℕ) : ℕ → Type where
  | input : Circuit inputs inputs
  | append {size : ℕ} (prior : Circuit inputs size)
      (coefficient : Fin size → ℝ) : Circuit inputs (size + 1)

namespace Circuit

def inputIndex {n d : ℕ} (c : Circuit n d) : Fin n → Fin d :=
  match c with
  | .input => id
  | .append prior _ => fun i => (prior.inputIndex i).castSucc

theorem inputIndex_injective {n d : ℕ} (c : Circuit n d) :
    Function.Injective c.inputIndex := by
  induction c with
  | input => exact Function.injective_id
  | @append d prior a ih =>
      intro i j h
      apply ih
      apply Fin.ext
      have hv := congrArg (fun x : Fin (d + 1) => x.val) h
      exact hv

theorem inputs_le_size {n d : ℕ} (c : Circuit n d) : n ≤ d := by
  induction c with
  | input => exact le_refl _
  | append prior a ih => exact ih.trans (Nat.le_succ _)

theorem inputIndex_value {n d : ℕ} (c : Circuit n d) (i : Fin n) :
    (c.inputIndex i).val = i.val := by
  induction c with
  | input => rfl
  | append prior a ih => exact ih

def evaluate {n d : ℕ} (c : Circuit n d) (input : Fin n → ℝ)
    (error : Fin d → ℝ) : Fin d → ℝ :=
  match c with
  | .input => input + error
  | .append prior coefficient =>
      let state := prior.evaluate input (fun i => error i.castSucc)
      Fin.snoc state ((∑ i, coefficient i * state i) + error (Fin.last _))

def residual {n d : ℕ} (c : Circuit n d) (input : Fin n → ℝ)
    (state : Fin d → ℝ) : Fin d → ℝ :=
  match c with
  | .input => state - input
  | .append prior coefficient =>
      Fin.snoc (prior.residual input (fun i => state i.castSucc))
        (state (Fin.last _) - ∑ i, coefficient i * state i.castSucc)

@[simp] theorem evaluate_input {n : ℕ} (input error : Fin n → ℝ) :
    (Circuit.input : Circuit n n).evaluate input error = input + error := rfl

@[simp] theorem evaluate_append_castSucc {n d : ℕ} (c : Circuit n d)
    (a : Fin d → ℝ) (input : Fin n → ℝ) (error : Fin (d + 1) → ℝ)
    (i : Fin d) :
    (c.append a).evaluate input error i.castSucc =
      c.evaluate input (fun j => error j.castSucc) i := by
  simp [evaluate]

@[simp] theorem evaluate_append_last {n d : ℕ} (c : Circuit n d)
    (a : Fin d → ℝ) (input : Fin n → ℝ) (error : Fin (d + 1) → ℝ) :
    (c.append a).evaluate input error (Fin.last d) =
      (∑ i, a i * c.evaluate input (fun j => error j.castSucc) i) +
        error (Fin.last d) := by
  simp [evaluate]

/-- A circuit never changes a previously allocated input coordinate. -/
theorem evaluate_at_input {n d : ℕ} (c : Circuit n d)
    (input : Fin n → ℝ) (error : Fin d → ℝ) (i : Fin n) :
    c.evaluate input error (c.inputIndex i) = input i + error (c.inputIndex i) := by
  induction c with
  | input => rfl
  | append prior a ih =>
      simp only [inputIndex, evaluate_append_castSucc]
      exact ih (fun j => error j.castSucc)

theorem residual_at_input {n d : ℕ} (c : Circuit n d)
    (input : Fin n → ℝ) (state : Fin d → ℝ) (i : Fin n) :
    c.residual input state (c.inputIndex i) = state (c.inputIndex i) - input i := by
  induction c with
  | input => rfl
  | append prior a ih =>
      simp only [inputIndex, residual, Fin.snoc_castSucc]
      exact ih (fun j => state j.castSucc)

/-- Forward evaluation solves every equation with its prescribed residual. -/
theorem residual_evaluate {n d : ℕ} (c : Circuit n d)
    (input : Fin n → ℝ) (error : Fin d → ℝ) :
    c.residual input (c.evaluate input error) = error := by
  induction c with
  | input => simp [residual, evaluate]
  | @append d prior a ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [residual, evaluate]
      · simpa [residual, evaluate] using congrFun (ih (fun j => error j.castSucc)) j

/-- Any approximate state is the exact forward evaluation of all of its
equation residuals. In particular, gate residuals are never silently zeroed. -/
theorem evaluate_residual {n d : ℕ} (c : Circuit n d)
    (input : Fin n → ℝ) (state : Fin d → ℝ) :
    c.evaluate input (c.residual input state) = state := by
  induction c with
  | input => simp [residual, evaluate]
  | @append d prior a ih =>
      have hp : (fun j : Fin d => (prior.append a).residual input state j.castSucc) =
          prior.residual input (fun j => state j.castSucc) := by
        funext j
        simp [residual]
      have he : prior.evaluate input
          (fun j : Fin d => (prior.append a).residual input state j.castSucc) =
          (fun j => state j.castSucc) := by
        rw [hp]
        exact ih (fun j => state j.castSucc)
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [evaluate_append_last, he]
        simp [residual]
      · rw [evaluate_append_castSucc, he]

/-- The equation map is bijective for every acyclic circuit and every input. -/
theorem residual_bijective {n d : ℕ} (c : Circuit n d)
    (input : Fin n → ℝ) : Function.Bijective (c.residual input) :=
  ⟨(Function.LeftInverse.injective (c.evaluate_residual input)),
    Function.RightInverse.surjective (c.residual_evaluate input)⟩

theorem evaluate_add {n d : ℕ} (c : Circuit n d)
    (x y : Fin n → ℝ) (r s : Fin d → ℝ) :
    c.evaluate (x + y) (r + s) = c.evaluate x r + c.evaluate y s := by
  induction c with
  | input => simp [evaluate]; abel
  | @append d prior a ih =>
      have hp := ih (fun i => r i.castSucc) (fun i => s i.castSucc)
      change prior.evaluate (x + y) (fun j => r j.castSucc + s j.castSucc) =
        prior.evaluate x (fun j => r j.castSucc) +
          prior.evaluate y (fun j => s j.castSucc) at hp
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Pi.add_apply, evaluate_append_last]
        rw [hp]
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        ring
      · simpa only [Pi.add_apply, evaluate_append_castSucc] using congrFun hp j

theorem evaluate_zero {n d : ℕ} (c : Circuit n d) :
    c.evaluate 0 0 = 0 := by
  have h := c.evaluate_add 0 0 0 0
  simpa using h.symm

theorem evaluate_smul {n d : ℕ} (c : Circuit n d) (t : ℝ)
    (x : Fin n → ℝ) (r : Fin d → ℝ) :
    c.evaluate (t • x) (t • r) = t • c.evaluate x r := by
  induction c with
  | input => simp [evaluate, smul_add]
  | @append d prior a ih =>
      have hp := ih (fun i => r i.castSucc)
      change prior.evaluate (t • x) (fun j => t * r j.castSucc) =
        t • prior.evaluate x (fun j => r j.castSucc) at hp
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Pi.smul_apply, smul_eq_mul, evaluate_append_last]
        rw [hp]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [mul_add, Finset.mul_sum]
        have hs : (∑ i, a i * (t * prior.evaluate x (fun j => r j.castSucc) i)) =
            ∑ i, t * (a i * prior.evaluate x (fun j => r j.castSucc) i) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hs]
      · simpa only [Pi.smul_apply, smul_eq_mul, evaluate_append_castSucc]
          using congrFun hp j

/-- Replace each edge weight by its magnitude, preserving the actual DAG. -/
def absoluteCoefficients {n d : ℕ} (c : Circuit n d) : Circuit n d :=
  match c with
  | .input => .input
  | .append prior a => prior.absoluteCoefficients.append (fun i => |a i|)

/-- The absolute weighted-path envelope bounds arbitrary simultaneous
perturbations. The envelope is computed by the same finite recursion. -/
theorem abs_evaluate_le_envelope {n d : ℕ} (c : Circuit n d)
    (input : Fin n → ℝ) (error : Fin d → ℝ) (i : Fin d) :
    |c.evaluate input error i| ≤
      c.absoluteCoefficients.evaluate (fun j => |input j|) (fun j => |error j|) i := by
  induction c with
  | input => simpa [evaluate, absoluteCoefficients] using abs_add_le (input i) (error i)
  | @append d prior a ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [evaluate_append_last, absoluteCoefficients]
        calc
          |(∑ j, a j * prior.evaluate input (fun k => error k.castSucc) j) +
              error (Fin.last d)| ≤
              |∑ j, a j * prior.evaluate input (fun k => error k.castSucc) j| +
                |error (Fin.last d)| := abs_add_le _ _
          _ ≤ (∑ j, |a j * prior.evaluate input (fun k => error k.castSucc) j|) +
                |error (Fin.last d)| := add_le_add (Finset.abs_sum_le_sum_abs _ _) (le_refl _)
          _ ≤ (∑ j, |a j| * prior.absoluteCoefficients.evaluate
                (fun k => |input k|) (fun k => |error k.castSucc|) j) +
                |error (Fin.last d)| := by
              apply add_le_add _ (le_refl _)
              apply Finset.sum_le_sum
              intro j _
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (ih (fun k => error k.castSucc) j) (abs_nonneg _)
          _ = _ := by simp
      · simpa [evaluate, absoluteCoefficients] using ih (fun k => error k.castSucc) j

/-- Error superposition at every node, including arbitrary input and gate errors. -/
theorem residual_error_superposition {n d : ℕ} (c : Circuit n d)
    (input : Fin n → ℝ) (state : Fin d → ℝ) :
    state = c.evaluate input 0 + c.evaluate 0 (c.residual input state) := by
  rw [← c.evaluate_add, add_zero, zero_add, c.evaluate_residual]

def copyGate {n d : ℕ} (c : Circuit n d) (parent : Fin d) : Circuit n (d + 1) :=
  c.append (fun i => if i = parent then 1 else 0)

def scaledGate {n d : ℕ} (c : Circuit n d) (parent : Fin d)
    (weight : ℝ) : Circuit n (d + 1) :=
  c.append (fun i => if i = parent then weight else 0)

def additionGate {n d : ℕ} (c : Circuit n d) (left right : Fin d) :
    Circuit n (d + 1) :=
  c.append (fun i => (if i = left then 1 else 0) + (if i = right then 1 else 0))

@[simp] theorem copyGate_last {n d : ℕ} (c : Circuit n d) (parent : Fin d)
    (input : Fin n → ℝ) (error : Fin (d + 1) → ℝ) :
    (c.copyGate parent).evaluate input error (Fin.last d) =
      c.evaluate input (fun i => error i.castSucc) parent + error (Fin.last d) := by
  simp [copyGate, evaluate_append_last]

@[simp] theorem scaledGate_last {n d : ℕ} (c : Circuit n d) (parent : Fin d)
    (weight : ℝ) (input : Fin n → ℝ) (error : Fin (d + 1) → ℝ) :
    (c.scaledGate parent weight).evaluate input error (Fin.last d) =
      weight * c.evaluate input (fun i => error i.castSucc) parent + error (Fin.last d) := by
  simp [scaledGate, evaluate_append_last, Finset.sum_ite_eq']

@[simp] theorem additionGate_last {n d : ℕ} (c : Circuit n d)
    (left right : Fin d) (input : Fin n → ℝ) (error : Fin (d + 1) → ℝ) :
    (c.additionGate left right).evaluate input error (Fin.last d) =
      c.evaluate input (fun i => error i.castSucc) left +
      c.evaluate input (fun i => error i.castSucc) right + error (Fin.last d) := by
  simp [additionGate, evaluate_append_last, add_mul, Finset.sum_add_distrib]

end Circuit
end Maxwell.Logical
