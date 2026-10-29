import Maxwell.Logical.Compile
import Maxwell.Logical.DyadicCompile

/-! Executable allocation of all rows of a finite dyadic matrix. -/

namespace Maxwell.Logical

noncomputable def Circuit.chargedList {n d : ℕ} (c : Circuit n d)
    (outputs : List (Fin d)) (k : Fin d) : ℕ := c.uses k + (outputs.map (Circuit.hit k)).sum

structure ForestCompilation {n d v : ℕ} (prior : Circuit n d)
    (inputIds : Fin v → Fin d) (expressions : List (Expression v)) where
  size : ℕ
  size_le : d ≤ size
  circuit : Circuit n size
  extension : prior.Extends circuit
  outputs : List (Fin size)
  output_count : outputs.length = expressions.length
  allocation : size = d + (expressions.map Expression.gateCount).sum
  preserves : ∀ (input : Fin n → ℝ) (i : Fin d),
    circuit.evaluate input 0 (Fin.castLE size_le i) = prior.evaluate input 0 i
  correct : ∀ input : Fin n → ℝ,
    outputs.map (circuit.evaluate input 0) =
      expressions.map (fun e => e.evaluate (fun i => prior.evaluate input 0 (inputIds i)))
  error_bound : (∀ e ∈ expressions, e.BoundedWeights) →
    ∀ (input : Fin n → ℝ) (error : Fin size → ℝ) (E : ℝ), 0 ≤ E →
    (∀ i, |error i| ≤ E) →
    List.Forall₂ (fun output e =>
      |circuit.evaluate input error output - e.evaluate
        (fun i => prior.evaluate input (fun j => error (Fin.castLE size_le j)) (inputIds i))| ≤
        (e.gateCount : ℝ) * E) outputs expressions
  charged_old : ∀ k : Fin d,
    circuit.chargedList outputs (Fin.castLE size_le k) ≤
      prior.uses k + (expressions.map (fun e => e.inputUses inputIds k)).sum
  charged_new : ∀ k : Fin size, d ≤ k.val → circuit.chargedList outputs k ≤ 1

/-- A verified forest step keeps recursive proof records abstract. -/
def compileForestStep {n d v : ℕ} (prior : Circuit n d) (inputIds : Fin v → Fin d)
    (e : Expression v) (es : List (Expression v))
    (head : ExpressionCompilation prior inputIds e)
    (tail : ForestCompilation head.circuit (fun i => Fin.castLE head.size_le (inputIds i)) es) :
    ForestCompilation prior inputIds (e :: es) := by
  let newInputs : Fin v → Fin head.size := fun i => Fin.castLE head.size_le (inputIds i)
  refine {
    size := tail.size
    size_le := head.size_le.trans tail.size_le
    circuit := tail.circuit
    extension := head.extension.trans tail.extension
    outputs := Fin.castLE tail.size_le head.output :: tail.outputs
    output_count := by simp only [List.length_cons, tail.output_count]
    allocation := ?_
    preserves := ?_
    correct := ?_
    error_bound := ?_
    charged_old := ?_
    charged_new := ?_ }
  · rw [tail.allocation, head.allocation]
    simp [Nat.add_assoc]
  · intro input i
    have hi : Fin.castLE (head.size_le.trans tail.size_le) i =
        Fin.castLE tail.size_le (Fin.castLE head.size_le i) := by apply Fin.ext; rfl
    rw [hi, tail.preserves, head.preserves]
  · intro input
    simp only [List.map_cons]
    rw [tail.preserves, head.correct, tail.correct]
    have hi : (fun i => head.circuit.evaluate input 0 (newInputs i)) =
        (fun i => prior.evaluate input 0 (inputIds i)) := by
      funext i
      exact head.preserves input (inputIds i)
    rw [hi]
  · intro hb input error E hE he
    let eh : Fin head.size → ℝ := fun i => error (Fin.castLE tail.size_le i)
    have hh := head.error_bound (hb e (by simp)) input eh E hE (fun i => he _)
    have ht := tail.error_bound (fun a hm => hb a (by simp [hm])) input error E hE he
    have hold : tail.circuit.evaluate input error (Fin.castLE tail.size_le head.output) =
        head.circuit.evaluate input eh head.output :=
      tail.extension.evaluate_old input error head.output
    have hv : (fun i => head.circuit.evaluate input
        (fun j => error (Fin.castLE tail.size_le j)) (newInputs i)) =
        (fun i => prior.evaluate input
          (fun j => error (Fin.castLE (head.size_le.trans tail.size_le) j)) (inputIds i)) := by
      funext i
      exact head.extension.evaluate_old input eh (inputIds i)
    refine List.Forall₂.cons ?_ ?_
    · rw [hold]
      simpa [eh, Fin.castLE] using hh
    · rw [hv] at ht
      exact ht
  · intro k
    let kh := Fin.castLE head.size_le k
    let kt := Fin.castLE tail.size_le kh
    have he : Fin.castLE (head.size_le.trans tail.size_le) k = kt := by apply Fin.ext; rfl
    have ht := tail.charged_old kh
    have hh := head.charged_old k
    have hv : (es.map (fun a => a.inputUses newInputs kh)).sum =
        (es.map (fun a => a.inputUses inputIds k)).sum := by
      congr 1
      apply List.map_congr_left
      intro a _
      exact a.inputUses_castLE inputIds head.size_le k
    have hhit : Circuit.hit kt (Fin.castLE tail.size_le head.output) =
        Circuit.hit kh head.output := Circuit.hit_castLE tail.size_le kh head.output
    rw [he]
    simp only [Circuit.chargedList, List.map_cons, List.sum_cons, hhit]
    rw [hv] at ht
    change tail.circuit.uses kt + (tail.outputs.map (Circuit.hit kt)).sum ≤
      head.circuit.uses kh + (es.map (fun a => a.inputUses inputIds k)).sum at ht
    change head.circuit.uses kh + Circuit.hit kh head.output ≤
      prior.uses k + e.inputUses inputIds k at hh
    omega
  · intro k hk
    by_cases hkh : k.val < head.size
    · let kh : Fin head.size := ⟨k.val, hkh⟩
      have he : k = Fin.castLE tail.size_le kh := by apply Fin.ext; rfl
      have ht := tail.charged_old kh
      have hh := head.charged_new kh hk
      have hvar (a : Expression v) : a.inputUses newInputs kh = 0 := by
        apply Expression.inputUses_zero
        intro i h
        have hv := congrArg (fun j : Fin head.size => j.val) h
        change k.val = (inputIds i).val at hv
        have hi := (inputIds i).isLt
        omega
      change tail.circuit.chargedList tail.outputs (Fin.castLE tail.size_le kh) ≤
        head.circuit.uses kh + (es.map (fun a => a.inputUses newInputs kh)).sum at ht
      simp only [hvar, List.map_const', List.sum_replicate, smul_zero, Nat.add_zero] at ht
      rw [he]
      simp only [Circuit.chargedList, List.map_cons, List.sum_cons, Circuit.hit_castLE]
      simp only [Circuit.chargedList] at ht
      simp only [Circuit.charged] at hh
      omega
    · have ht := tail.charged_new k (Nat.le_of_not_gt hkh)
      have hne : k ≠ Fin.castLE tail.size_le head.output := by
        intro h
        have hv := congrArg (fun j : Fin tail.size => j.val) h
        change k.val = head.output.val at hv
        have ho := head.output.isLt
        omega
      simpa [Circuit.chargedList, Circuit.hit, hne] using ht

/-- Executable sequential allocation of all rows. -/
def compileForest {n d v : ℕ} (expressions : List (Expression v))
    (prior : Circuit n d) (inputIds : Fin v → Fin d) :
    ForestCompilation prior inputIds expressions :=
  match expressions with
  | [] => by
      exact {
        size := d
        size_le := le_refl _
        circuit := prior
        extension := .refl
        outputs := []
        output_count := rfl
        allocation := by simp
        preserves := by intro input i; rfl
        correct := by intro input; rfl
        error_bound := by intro _ _ _ _ _ _; exact .nil
        charged_old := by intro k; simp [Circuit.chargedList]
        charged_new := by intro k hk; exact False.elim (Nat.not_lt_of_ge hk k.isLt) }
  | e :: es =>
      let head := compileExpression e prior inputIds
      let tail := compileForest es head.circuit (fun i => Fin.castLE head.size_le (inputIds i))
      compileForestStep prior inputIds e es head tail

/-- The total number of gates charges every nonzero occurrence and every
row, including empty rows. -/
theorem dyadic_forest_allocation {n d v : ℕ} (rows : List (List (DyadicTerm v)))
    (prior : Circuit n d) (inputIds : Fin v → Fin d) (precision : ℕ)
    (h : ∀ row ∈ rows, ∀ term ∈ row, term.bits.length ≤ precision) :
    (compileForest (rows.map rowExpression) prior inputIds).size ≤
      d + (rows.map List.length).sum * (2 * precision + 3) + rows.length := by
  rw [(compileForest (rows.map rowExpression) prior inputIds).allocation]
  have hs : ((rows.map rowExpression).map Expression.gateCount).sum ≤
      (rows.map List.length).sum * (2 * precision + 3) + rows.length := by
    induction rows with
    | nil => simp
    | cons row rows ih =>
        have hr := rowExpression_gateCount row precision (h row (by simp))
        have ht := ih (fun r hm => h r (by simp [hm]))
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        nlinarith
  omega

end Maxwell.Logical
