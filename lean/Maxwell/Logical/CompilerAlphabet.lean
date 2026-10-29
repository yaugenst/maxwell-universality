import Maxwell.Logical.CompilerFanout

/-! The actual occurrence-separated compiler uses only constant-size gates.
In particular, the two parents of every addition are distinct, so addition
does not silently create a coefficient of magnitude two. -/

namespace Maxwell.Logical

def AllowedWeight (w : ℝ) : Prop := w = 1 ∨ w = -1 ∨ w = 1 / 2 ∨ w = -1 / 2

namespace Circuit

inductive SmallGates {n : ℕ} : {d : ℕ} → Circuit n d → Prop where
  | input : SmallGates (.input : Circuit n n)
  | zero {d : ℕ} {c : Circuit n d} (h : SmallGates c) : SmallGates (c.append 0)
  | scale {d : ℕ} {c : Circuit n d} (h : SmallGates c) (parent : Fin d)
      (weight : ℝ) (hw : AllowedWeight weight) : SmallGates (c.scaledGate parent weight)
  | add {d : ℕ} {c : Circuit n d} (h : SmallGates c) (left right : Fin d)
      (hne : left ≠ right) : SmallGates (c.additionGate left right)

theorem CopyOnly.smallGates {n d : ℕ} {c : Circuit n d} (h : c.CopyOnly) : c.SmallGates := by
  induction h with
  | input => exact .input
  | copy h parent ih =>
      simpa only [copyGate, scaledGate] using ih.scale parent 1 (Or.inl rfl)

end Circuit

namespace Expression

def FiniteWeights {v : ℕ} : Expression v → Prop
  | .var _ => True
  | .zero => True
  | .scale w e => AllowedWeight (w : ℝ) ∧ e.FiniteWeights
  | .add a b => a.FiniteWeights ∧ b.FiniteWeights

def LinearInputs {v d : ℕ} (e : Expression v) (ids : Fin v → Fin d) : Prop :=
  ∀ k, e.inputUses ids k ≤ 1

theorem LinearInputs.castLE {v d s : ℕ} {e : Expression v} {ids : Fin v → Fin d}
    (h : e.LinearInputs ids) (hds : d ≤ s) :
    e.LinearInputs (fun i => Fin.castLE hds (ids i)) := by
  intro k
  by_cases hk : k.val < d
  · let j : Fin d := ⟨k.val, hk⟩
    have he : k = Fin.castLE hds j := by apply Fin.ext; rfl
    rw [he, e.inputUses_castLE]
    exact h j
  · rw [e.inputUses_zero]
    · omega
    · intro i hi
      have hv := congrArg Fin.val hi
      have hj := (ids i).isLt
      simp only [Fin.val_castLE] at hv
      omega

theorem inputUses_pos {v d : ℕ} (e : Expression v) (ids : Fin v → Fin d)
    (k : Fin d) (h : 0 < e.inputUses ids k) : ∃ i, k = ids i := by
  by_contra hn
  have hz := e.inputUses_zero ids k (fun i hi => hn ⟨i, hi⟩)
  omega

@[simp] theorem rename_finiteWeights {v w : ℕ} (f : Fin v → Fin w) (e : Expression v) :
    (e.rename f).FiniteWeights ↔ e.FiniteWeights := by
  induction e with
  | var i => rfl
  | zero => rfl
  | scale a e ih => simp [rename, FiniteWeights, ih]
  | add a b iha ihb => simp [rename, FiniteWeights, iha, ihb]

theorem linearized_finiteWeights {v : ℕ} (e : Expression v) :
    e.linearized.FiniteWeights ↔ e.FiniteWeights := by
  induction e with
  | var i => rfl
  | zero => rfl
  | scale a e ih =>
      change (AllowedWeight (a : ℝ) ∧ e.linearized.FiniteWeights) ↔ _
      rw [ih]
      rfl
  | add a b iha ihb =>
      dsimp only [linearized, leafCount, FiniteWeights]
      rw [rename_finiteWeights, rename_finiteWeights, iha, ihb]

end Expression

theorem ExpressionCompilation.output_inputUse {n d v : ℕ} {prior : Circuit n d}
    {ids : Fin v → Fin d} {e : Expression v} (result : ExpressionCompilation prior ids e)
    (k : Fin d) (hk : result.output = Fin.castLE result.size_le k) :
    1 ≤ e.inputUses ids k := by
  have h := result.charged_old k
  have hm := result.extension.uses_old_mono k
  simp only [Circuit.charged, hk, Circuit.hit, ite_true] at h
  omega

theorem addition_parents_distinct {n d v : ℕ} {prior : Circuit n d}
    {ids : Fin v → Fin d} {left right : Expression v}
    (h : (Expression.add left right).LinearInputs ids)
    (l : ExpressionCompilation prior ids left)
    (r : ExpressionCompilation l.circuit (fun i => Fin.castLE l.size_le (ids i)) right) :
    Fin.castLE r.size_le l.output ≠ r.output := by
  intro he
  have hr := r.output_inputUse l.output he.symm
  obtain ⟨i, hi⟩ := right.inputUses_pos (fun i => Fin.castLE l.size_le (ids i))
    l.output (by omega)
  have hl := l.output_inputUse (ids i) hi
  rw [hi, right.inputUses_castLE] at hr
  have ht := h (ids i)
  change left.inputUses ids (ids i) + right.inputUses ids (ids i) ≤ 1 at ht
  omega

theorem compileExpression_smallGates {n d v : ℕ} (e : Expression v)
    (prior : Circuit n d) (ids : Fin v → Fin d) (hp : prior.SmallGates)
    (hw : e.FiniteWeights) (hi : e.LinearInputs ids) :
    (compileExpression e prior ids).circuit.SmallGates := by
  induction e generalizing d with
  | var i => exact hp
  | zero => exact hp.zero
  | scale a e ih =>
      exact (ih prior ids hp hw.2 hi).scale _ a hw.1
  | add a b iha ihb =>
      let l := compileExpression a prior ids
      let r := compileExpression b l.circuit (fun i => Fin.castLE l.size_le (ids i))
      have ha : a.LinearInputs ids := by intro k; have := hi k; change _ + _ ≤ 1 at this; omega
      have hb : b.LinearInputs ids := by intro k; have := hi k; change _ + _ ≤ 1 at this; omega
      have hl : l.circuit.SmallGates := iha prior ids hp hw.1 ha
      have hr : r.circuit.SmallGates := ihb l.circuit _ hl hw.2 (hb.castLE l.size_le)
      exact hr.add _ _ (addition_parents_distinct hi l r)

theorem compileForest_smallGates {n d v : ℕ} (es : List (Expression v))
    (prior : Circuit n d) (ids : Fin v → Fin d) (hp : prior.SmallGates)
    (hw : ∀ e ∈ es, e.FiniteWeights) (hi : ∀ e ∈ es, e.LinearInputs ids) :
    (compileForest es prior ids).circuit.SmallGates := by
  induction es generalizing d with
  | nil => exact hp
  | cons e es ih =>
      let head := compileExpression e prior ids
      have hh : head.circuit.SmallGates :=
        compileExpression_smallGates e prior ids hp (hw e (by simp)) (hi e (by simp))
      exact ih head.circuit _ hh (fun a ha => hw a (by simp [ha]))
        (fun a ha => (hi a (by simp [ha])).castLE head.size_le)

theorem linearizedRows_finiteWeights {n : ℕ} (rows : List (Expression n))
    (h : ∀ e ∈ rows, e.FiniteWeights) :
    ∀ e ∈ linearizedRows rows, e.FiniteWeights := by
  induction rows with
  | nil => simp [linearizedRows]
  | cons e es ih =>
      intro a ha
      dsimp only [linearizedRows, forestLeafCount] at ha
      rcases List.mem_cons.mp ha with he | he
      · subst a
        exact (Expression.rename_finiteWeights _ _).2 ((e.linearized_finiteWeights).2 (h e (by simp)))
      · rcases List.mem_map.mp he with ⟨b, hb, hab⟩
        rw [← hab]
        exact (Expression.rename_finiteWeights _ _).2 (ih (fun c hc => h c (by simp [hc])) b hb)

theorem compileCopiedForest_smallGates {n : ℕ} (rows : List (Expression n))
    (h : ∀ e ∈ rows, e.FiniteWeights) : (compileCopiedForest rows).circuit.SmallGates := by
  apply compileForest_smallGates
  · exact (forestCopies rows).bank.copy_only.smallGates
  · exact linearizedRows_finiteWeights rows h
  · intro e he k
    have hs := linearizedRows_inputUses_le_one rows (copiedForestInputs rows)
      (copiedForestInputs_injective rows) k
    exact (List.single_le_sum (fun _ _ => Nat.zero_le _) _
      (List.mem_map.mpr ⟨e, he, rfl⟩)).trans hs

theorem Horner.expression_finiteWeights {v : ℕ} (input : Fin v) (bits : List Bool) :
    (Horner.expression input bits).FiniteWeights := by
  induction bits with
  | nil => trivial
  | cons b bits ih =>
      cases b <;> norm_num [Horner.expression, Expression.FiniteWeights, AllowedWeight, ih]

theorem DyadicTerm.expression_finiteWeights {v : ℕ} (term : DyadicTerm v) :
    term.expression.FiniteWeights := by
  cases hb : term.negative <;> simp [DyadicTerm.expression, hb, Expression.FiniteWeights,
    AllowedWeight, Horner.expression_finiteWeights]

theorem rowExpression_finiteWeights {v : ℕ} (terms : List (DyadicTerm v)) :
    (rowExpression terms).FiniteWeights := by
  induction terms with
  | nil => trivial
  | cons term terms ih => exact ⟨term.expression_finiteWeights, ih⟩

theorem sourceCircuit_smallGates (S : Source.SparseSystem) (precision : ℕ) :
    (sourceCircuit S precision).circuit.SmallGates := by
  apply compileCopiedForest_smallGates
  intro e he
  obtain ⟨terms, _, rfl⟩ := List.mem_map.mp he
  exact rowExpression_finiteWeights terms

end Maxwell.Logical
