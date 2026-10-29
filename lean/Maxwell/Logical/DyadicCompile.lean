import Maxwell.Logical.Compile
import Maxwell.Logical.Horner

/-! Binary dyadics compiled into actual finite gate allocations. The only
arithmetic weights introduced here are `1/2` and the optional sign `-1`.
-/

namespace Maxwell.Logical.Horner

def expression {v : ℕ} (input : Fin v) : List Bool → Expression v
  | [] => .zero
  | false :: bits => .scale (1 / 2) (expression input bits)
  | true :: bits => .scale (1 / 2) (.add (.var input) (expression input bits))

theorem expression_gateCount (v : ℕ) (input : Fin v) (bits : List Bool) :
    (expression input bits).gateCount ≤ 2 * bits.length + 1 := by
  induction bits with
  | nil => simp [expression, Expression.gateCount]
  | cons b bits ih =>
      cases b <;> simp only [expression, Expression.gateCount, List.length_cons] <;> omega

theorem expression_bounded {v : ℕ} (input : Fin v) (bits : List Bool) :
    (expression input bits).BoundedWeights := by
  induction bits with
  | nil => trivial
  | cons b bits ih =>
      cases b <;> norm_num [expression, Expression.BoundedWeights, ih]

theorem expression_correct {v : ℕ} (input : Fin v) (bits : List Bool)
    (values : Fin v → ℝ) :
    (expression input bits).evaluate values = (coefficient bits : ℝ) * values input := by
  induction bits with
  | nil => simp [expression, Expression.evaluate, coefficient]
  | cons b bits ih =>
      cases b <;> simp [expression, Expression.evaluate, coefficient, ih] <;> ring

/-- Complete finite gate allocation for one dyadic coefficient product. -/
def compile {n d v : ℕ} (prior : Circuit n d) (inputIds : Fin v → Fin d)
    (input : Fin v) (bits : List Bool) :
    ExpressionCompilation prior inputIds (expression input bits) :=
  compileExpression (expression input bits) prior inputIds

theorem compile_size {n d v : ℕ} (prior : Circuit n d) (inputIds : Fin v → Fin d)
    (input : Fin v) (bits : List Bool) :
    (compile prior inputIds input bits).size ≤ d + 2 * bits.length + 1 := by
  rw [(compile prior inputIds input bits).allocation]
  have h := expression_gateCount v input bits
  omega

theorem compile_value {n d v : ℕ} (prior : Circuit n d) (inputIds : Fin v → Fin d)
    (input : Fin v) (bits : List Bool) (source : Fin n → ℝ) :
    (compile prior inputIds input bits).circuit.evaluate source 0
        (compile prior inputIds input bits).output =
      (coefficient bits : ℝ) * prior.evaluate source 0 (inputIds input) := by
  rw [(compile prior inputIds input bits).correct, expression_correct]

end Maxwell.Logical.Horner

namespace Maxwell.Logical

structure DyadicTerm (v : ℕ) where
  bits : List Bool
  negative : Bool
  input : Fin v

namespace DyadicTerm

def expression {v : ℕ} (term : DyadicTerm v) : Expression v :=
  if term.negative then .scale (-1) (Horner.expression term.input term.bits)
  else Horner.expression term.input term.bits

def coefficient {v : ℕ} (term : DyadicTerm v) : ℚ :=
  if term.negative then -Horner.coefficient term.bits else Horner.coefficient term.bits

theorem expression_correct {v : ℕ} (term : DyadicTerm v) (values : Fin v → ℝ) :
    term.expression.evaluate values = (term.coefficient : ℝ) * values term.input := by
  cases h : term.negative <;>
    simp [expression, coefficient, h, Expression.evaluate, Horner.expression_correct]

theorem expression_gateCount {v : ℕ} (term : DyadicTerm v) :
    term.expression.gateCount ≤ 2 * term.bits.length + 2 := by
  have h := Horner.expression_gateCount v term.input term.bits
  cases hb : term.negative <;> simp only [expression, hb, Bool.false_eq_true,
    ↓reduceIte, Expression.gateCount] <;> omega

theorem expression_bounded {v : ℕ} (term : DyadicTerm v) :
    term.expression.BoundedWeights := by
  cases hb : term.negative <;> simp [expression, hb, Expression.BoundedWeights,
    Horner.expression_bounded]

end DyadicTerm

def rowExpression {v : ℕ} : List (DyadicTerm v) → Expression v
  | [] => .zero
  | term :: terms => .add term.expression (rowExpression terms)

theorem rowExpression_correct {v : ℕ} (terms : List (DyadicTerm v))
    (values : Fin v → ℝ) :
    (rowExpression terms).evaluate values =
      (terms.map (fun term => (term.coefficient : ℝ) * values term.input)).sum := by
  induction terms with
  | nil => simp [rowExpression, Expression.evaluate]
  | cons term terms ih =>
      simp [rowExpression, Expression.evaluate, term.expression_correct, ih]

theorem rowExpression_bounded {v : ℕ} (terms : List (DyadicTerm v)) :
    (rowExpression terms).BoundedWeights := by
  induction terms with
  | nil => trivial
  | cons term terms ih => exact ⟨term.expression_bounded, ih⟩

/-- Linear total allocation for a sparse row. Empty rows also have an
explicit one-gate constant output. -/
theorem rowExpression_gateCount {v : ℕ} (terms : List (DyadicTerm v)) (precision : ℕ)
    (h : ∀ term ∈ terms, term.bits.length ≤ precision) :
    (rowExpression terms).gateCount ≤ terms.length * (2 * precision + 3) + 1 := by
  induction terms with
  | nil => simp [rowExpression, Expression.gateCount]
  | cons term terms ih =>
      have ht : term.bits.length ≤ precision := h term (by simp)
      have htail := ih (fun t hm => h t (by simp [hm]))
      have hg := term.expression_gateCount
      simp only [rowExpression, Expression.gateCount, List.length_cons]
      nlinarith

end Maxwell.Logical
