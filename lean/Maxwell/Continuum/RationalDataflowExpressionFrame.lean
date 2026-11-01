import Maxwell.Continuum.RationalDataflowExpression

/-! Polynomial scratch evaluation preserves the literal input representation,
not only its rational value. This keeps row-wise input width bounds stable. -/
namespace Maxwell.Continuum.RationalDataflow.PolynomialExpression
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem instructions_keep (e : PolynomialExpression) (base : ℕ) (v : ℕ → Parts)
    (i : ℕ) (hi : i<base) : RationalDataflow.evaluate (e.instructions base) v i=v i := by
  induction e generalizing base v with
  | literal q =>
    simp only [instructions,RationalDataflow.evaluate,Instruction.update,
      Function.update_of_ne (by omega : i≠base)]
  | inputRegister j =>
    simp only [instructions,RationalDataflow.evaluate,Instruction.update,
      Function.update_of_ne (by omega : i≠base)]
  | binary op x y hx hy =>
    simp only [instructions,evaluate_append,RationalDataflow.evaluate,Instruction.update,
      Function.update_of_ne (by omega : i≠base)]
    exact (hy (base+1) _ (by omega)).trans (hx base v hi)

theorem control_keep (e : PolynomialExpression) (base : ℕ) (v : ℕ → Parts)
    (i : ℕ) (hi : i<base) : (e.control base).evaluate v i=v i := by
  rw [control,Control.prepend_evaluate]
  exact e.instructions_keep base v i hi

#print axioms control_keep
end Maxwell.Continuum.RationalDataflow.PolynomialExpression
