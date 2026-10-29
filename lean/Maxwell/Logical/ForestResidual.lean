import Maxwell.Logical.Forest

namespace Maxwell.Logical

theorem forall₂_imp_right_mem {A B : Type*} {R T : A → B → Prop}
    {xs : List A} {ys : List B} (h : List.Forall₂ R xs ys)
    (f : ∀ a b, b ∈ ys → R a b → T a b) : List.Forall₂ T xs ys := by
  induction h with
  | nil => exact .nil
  | @cons a b xs ys hab htail ih =>
      exact .cons (f a b (by simp) hab) (ih (fun x y hy => f x y (by simp [hy])))

theorem ForestCompilation.arbitrary_residual {n d v : ℕ} {prior : Circuit n d}
    {inputIds : Fin v → Fin d} {expressions : List (Expression v)}
    (result : ForestCompilation prior inputIds expressions)
    (hb : ∀ e ∈ expressions, e.BoundedWeights) (input : Fin n → ℝ)
    (state : Fin result.size → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (he : ∀ i, |result.circuit.residual input state i| ≤ E) :
    List.Forall₂ (fun output e =>
      |state output - e.evaluate (fun i => state (Fin.castLE result.size_le (inputIds i)))| ≤
        (e.gateCount : ℝ) * E) result.outputs expressions := by
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

end Maxwell.Logical
