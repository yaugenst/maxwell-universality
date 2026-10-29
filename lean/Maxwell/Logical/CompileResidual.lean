import Maxwell.Logical.Compile

namespace Maxwell.Logical.ExpressionCompilation

/-- The implemented compiler controls the defect for every assignment of
all auxiliary variables. No exact-gate premise is present. -/
theorem arbitrary_residual {n d v : ℕ} {prior : Circuit n d}
    {inputIds : Fin v → Fin d} {expression : Expression v}
    (result : ExpressionCompilation prior inputIds expression)
    (hb : expression.BoundedWeights) (input : Fin n → ℝ)
    (state : Fin result.size → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (he : ∀ i, |result.circuit.residual input state i| ≤ E) :
    |state result.output - expression.evaluate
      (fun i => state (Fin.castLE result.size_le (inputIds i)))| ≤
        (expression.gateCount : ℝ) * E := by
  have h := result.error_bound hb input (result.circuit.residual input state) E hE he
  rw [result.circuit.evaluate_residual] at h
  have hi : (fun i => prior.evaluate input
      (fun j => result.circuit.residual input state (Fin.castLE result.size_le j))
      (inputIds i)) = (fun i => state (Fin.castLE result.size_le (inputIds i))) := by
    funext i
    rw [← result.extension.evaluate_old input (result.circuit.residual input state),
      result.circuit.evaluate_residual]
  rw [hi] at h
  exact h

end Maxwell.Logical.ExpressionCompilation
