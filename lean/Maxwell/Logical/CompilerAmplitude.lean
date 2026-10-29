import Maxwell.Logical.SourceCircuit

/-! Bounds on every allocated coordinate of the actual expression/forest
compiler. Old coordinates are preserved, and each new coordinate is the
output of an actual bounded-weight subtree. -/
namespace Maxwell.Logical

private def nodeBudget (g : ℕ) (X E : ℝ) : ℝ := (g + 1) * X + g * E

private theorem nodeBudget_mono {g h : ℕ} (hgh : g ≤ h) {X E : ℝ}
    (hX : 0 ≤ X) (hE : 0 ≤ E) : nodeBudget g X E ≤ nodeBudget h X E := by
  have h : (g : ℝ) ≤ h := by exact_mod_cast hgh
  unfold nodeBudget
  nlinarith [mul_le_mul_of_nonneg_right h hX, mul_le_mul_of_nonneg_right h hE]

theorem Expression.evaluate_abs_le {v : ℕ} (e : Expression v) (hb : e.BoundedWeights)
    (x : Fin v → ℝ) (X : ℝ) (hX : 0 ≤ X) (hx : ∀ i, |x i| ≤ X) :
    |e.evaluate x| ≤ ((e.gateCount : ℝ) + 1) * X := by
  induction e with
  | var i => simpa [Expression.evaluate, Expression.gateCount] using hx i
  | zero => simpa [Expression.evaluate, Expression.gateCount] using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hX)
  | scale a e ih =>
      have h := (mul_le_mul hb.1 (ih hb.2) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
      simp only [one_mul] at h
      simp only [Expression.evaluate, Expression.gateCount, Nat.cast_add, Nat.cast_one, abs_mul]
      nlinarith
  | add a b iha ihb =>
      have h := (abs_add_le (a.evaluate x) (b.evaluate x)).trans (add_le_add (iha hb.1) (ihb hb.2))
      convert h using 1 <;> simp only [Expression.evaluate, Expression.gateCount, Nat.cast_add, Nat.cast_one]
      ring

private theorem expression_output_bound {n d v : ℕ} {prior : Circuit n d}
    {ids : Fin v → Fin d} {e : Expression v} (c : ExpressionCompilation prior ids e)
    (hb : e.BoundedWeights) (input : Fin n → ℝ) (error : Fin c.size → ℝ)
    (X E : ℝ) (hX : 0 ≤ X) (hE : 0 ≤ E) (he : ∀ i, |error i| ≤ E)
    (hx : ∀ i, |prior.evaluate input (fun j => error (Fin.castLE c.size_le j)) (ids i)| ≤ X) :
    |c.circuit.evaluate input error c.output| ≤ nodeBudget e.gateCount X E := by
  have hr := c.error_bound hb input error E hE he
  have ha := e.evaluate_abs_le hb _ X hX hx
  calc
    _ ≤ |c.circuit.evaluate input error c.output - e.evaluate _| + |e.evaluate _| :=
      by simpa using abs_sub_le (c.circuit.evaluate input error c.output) (e.evaluate _) 0
    _ ≤ (e.gateCount : ℝ) * E + ((e.gateCount : ℝ) + 1) * X := add_le_add hr ha
    _ = _ := by unfold nodeBudget; ring

/-- All states, not merely the selected output, are bounded for the actual
recursive compiler. The bound on original selected inputs stays fixed even
when previous subtrees have already been allocated. -/
theorem compileExpression_all_bound {n d v : ℕ} (e : Expression v) (hb : e.BoundedWeights)
    (prior : Circuit n d) (ids : Fin v → Fin d) (input : Fin n → ℝ)
    (B X E : ℝ) (hX : 0 ≤ X) (hE : 0 ≤ E)
    (hprior : ∀ error : Fin d → ℝ, (∀ j, |error j| ≤ E) → ∀ j, |prior.evaluate input error j| ≤ B)
    (hinput : ∀ error : Fin d → ℝ, (∀ j, |error j| ≤ E) → ∀ i, |prior.evaluate input error (ids i)| ≤ X) :
    ∀ error : Fin (compileExpression e prior ids).size → ℝ, (∀ j, |error j| ≤ E) →
      ∀ j, |(compileExpression e prior ids).circuit.evaluate input error j| ≤
        max B (nodeBudget e.gateCount X E) := by
  induction e generalizing d B with
  | var i =>
      intro error he j
      exact (hprior error he j).trans (le_max_left _ _)
  | zero =>
      intro error he j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · exact (expression_output_bound (compileExpression .zero prior ids) hb input error X E hX hE he
          (hinput _ (fun i => he _))).trans (le_max_right _ _)
      · change |(prior.append 0).evaluate input error i.castSucc| ≤ _
        erw [Circuit.evaluate_append_castSucc]
        exact (hprior _ (fun i => he _) i).trans (le_max_left _ _)
  | scale a e ih =>
      let c := compileExpression e prior ids
      intro error he j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · exact (expression_output_bound (compileExpression (.scale a e) prior ids) hb input error X E hX hE he
          (hinput _ (fun i => he _))).trans (le_max_right _ _)
      · change |(c.circuit.append _).evaluate input error i.castSucc| ≤ _
        erw [Circuit.evaluate_append_castSucc]
        exact (ih hb.2 prior ids B hprior hinput _ (fun i => he _) i).trans
          (max_le_max (le_refl B) (nodeBudget_mono (by simp only [Expression.gateCount]; omega) hX hE))
  | add a b iha ihb =>
      let ca := compileExpression a prior ids
      let newIds : Fin v → Fin ca.size := fun i => Fin.castLE ca.size_le (ids i)
      let cb := compileExpression b ca.circuit newIds
      have hca : ∀ error : Fin ca.size → ℝ, (∀ j, |error j| ≤ E) →
          ∀ j, |ca.circuit.evaluate input error j| ≤ max B (nodeBudget a.gateCount X E) :=
        iha hb.1 prior ids B hprior hinput
      have hcaInput : ∀ error : Fin ca.size → ℝ, (∀ j, |error j| ≤ E) →
          ∀ i, |ca.circuit.evaluate input error (newIds i)| ≤ X := by
        intro error he i
        rw [show newIds i = Fin.castLE ca.extension.size_le (ids i) from rfl,
          ca.extension.evaluate_old]
        exact hinput _ (fun j => he _) i
      intro error he j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · exact (expression_output_bound (compileExpression (.add a b) prior ids) hb input error X E hX hE he
          (hinput _ (fun i => he _))).trans (le_max_right _ _)
      · change |(cb.circuit.append _).evaluate input error i.castSucc| ≤ _
        erw [Circuit.evaluate_append_castSucc]
        have hi := ihb hb.2 ca.circuit newIds (max B (nodeBudget a.gateCount X E))
          hca hcaInput (fun k => error k.castSucc) (fun k => he k.castSucc) i
        apply hi.trans
        apply max_le
        · apply max_le (le_max_left _ _)
          exact (nodeBudget_mono (by simp only [Expression.gateCount]; omega) hX hE).trans (le_max_right _ _)
        · exact (nodeBudget_mono (by simp only [Expression.gateCount]; omega) hX hE).trans (le_max_right _ _)

/-- Forest rows all continue to reference the original inputs. Hence the
maximum row allocation, rather than repeated multiplication across rows,
controls every intermediate coordinate. -/
theorem compileForest_all_bound {n d v : ℕ} (rows : List (Expression v))
    (hb : ∀ e ∈ rows, e.BoundedWeights) (G : ℕ) (hg : ∀ e ∈ rows, e.gateCount ≤ G)
    (prior : Circuit n d) (ids : Fin v → Fin d) (input : Fin n → ℝ)
    (B X E : ℝ) (hX : 0 ≤ X) (hE : 0 ≤ E)
    (hprior : ∀ error : Fin d → ℝ, (∀ j, |error j| ≤ E) → ∀ j, |prior.evaluate input error j| ≤ B)
    (hinput : ∀ error : Fin d → ℝ, (∀ j, |error j| ≤ E) → ∀ i, |prior.evaluate input error (ids i)| ≤ X) :
    ∀ error : Fin (compileForest rows prior ids).size → ℝ, (∀ j, |error j| ≤ E) →
      ∀ j, |(compileForest rows prior ids).circuit.evaluate input error j| ≤
        max B (nodeBudget G X E) := by
  induction rows generalizing d B with
  | nil =>
      intro error he j
      exact (hprior error he j).trans (le_max_left _ _)
  | cons e rows ih =>
      let head := compileExpression e prior ids
      let newIds : Fin v → Fin head.size := fun i => Fin.castLE head.size_le (ids i)
      have hhead : ∀ error : Fin head.size → ℝ, (∀ j, |error j| ≤ E) →
          ∀ j, |head.circuit.evaluate input error j| ≤ max B (nodeBudget G X E) := by
        intro error he j
        exact (compileExpression_all_bound e (hb e (by simp)) prior ids input B X E hX hE
          hprior hinput error he j).trans
          (max_le_max (le_refl B) (nodeBudget_mono (hg e (by simp)) hX hE))
      have hheadInput : ∀ error : Fin head.size → ℝ, (∀ j, |error j| ≤ E) →
          ∀ i, |head.circuit.evaluate input error (newIds i)| ≤ X := by
        intro error he i
        rw [show newIds i = Fin.castLE head.extension.size_le (ids i) from rfl,
          head.extension.evaluate_old]
        exact hinput _ (fun j => he _) i
      intro error he j
      have h := ih (fun a ha => hb a (by simp [ha])) (fun a ha => hg a (by simp [ha]))
        head.circuit newIds (max B (nodeBudget G X E)) hhead hheadInput error he j
      exact h.trans (max_le (le_refl _) (le_max_right _ _))

/-- Uniform amplitude bound for every actual copy-bank and arithmetic node.
It charges all simultaneous residuals, including errors in the copy bank. -/
theorem compileCopiedForest_evaluate_bound {n : ℕ} (rows : List (Expression n))
    (hb : ∀ e ∈ rows, e.BoundedWeights) (input : Fin n → ℝ) (X E : ℝ)
    (hX : 0 ≤ X) (hE : 0 ≤ E) (hx : ∀ i, |input i| ≤ X)
    (error : Fin (compileCopiedForest rows).size → ℝ) (he : ∀ j, |error j| ≤ E)
    (j : Fin (compileCopiedForest rows).size) :
    |(compileCopiedForest rows).circuit.evaluate input error j| ≤
      (((compileCopiedForest rows).size : ℝ) + 1) * X +
        (((compileCopiedForest rows).size : ℝ) + 1)^2 * E := by
  let bank := (forestCopies rows).bank
  let G := ((linearizedRows rows).map Expression.gateCount).sum
  let B : ℝ := X + (bank.size : ℝ) * E
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbank : ∀ err : Fin bank.size → ℝ, (∀ i, |err i| ≤ E) →
      ∀ i, |bank.circuit.evaluate input err i| ≤ B := by
    intro err herr i
    have h := bank.copy_only.evaluate_bound input err X hx i
    apply h.trans
    dsimp [B]
    apply add_le_add (le_refl X)
    calc
      ∑ i, |err i| ≤ ∑ _i : Fin bank.size, E := Finset.sum_le_sum (fun i _ => herr i)
      _ = _ := by simp
  have hg (e : Expression (forestLeafCount rows)) (hem : e ∈ linearizedRows rows) :
      e.gateCount ≤ G := List.le_sum_of_mem (List.mem_map.mpr ⟨e, hem, rfl⟩)
  have h := compileForest_all_bound (linearizedRows rows) (linearizedRows_bounded rows hb) G hg
    bank.circuit (copiedForestInputs rows) input B B E hB hE hbank
    (fun err herr i => hbank err herr _) error he j
  have hgs : G ≤ (compileCopiedForest rows).size := by
    have ha := (compileCopiedForest rows).allocation
    change (compileCopiedForest rows).size = bank.size + G at ha
    omega
  have hbs : bank.size ≤ (compileCopiedForest rows).size := (compileCopiedForest rows).size_le
  have hBupper : B ≤ X + ((compileCopiedForest rows).size : ℝ) * E := by
    dsimp [B]
    exact add_le_add (le_refl X) (mul_le_mul_of_nonneg_right (by exact_mod_cast hbs) hE)
  have hs0 : (0 : ℝ) ≤ (compileCopiedForest rows).size := Nat.cast_nonneg _
  have hbudget : nodeBudget G B E ≤
      (((compileCopiedForest rows).size : ℝ) + 1) * X +
        (((compileCopiedForest rows).size : ℝ) + 1)^2 * E := by
    apply (nodeBudget_mono hgs hB hE).trans
    unfold nodeBudget
    have hm := mul_le_mul_of_nonneg_left hBupper (show 0 ≤ ((compileCopiedForest rows).size : ℝ) + 1 by positivity)
    nlinarith
  apply h.trans
  apply max_le _ hbudget
  have hBg : B ≤ nodeBudget G B E := by
    unfold nodeBudget
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ G by positivity) hB,
      mul_nonneg (show (0 : ℝ) ≤ G by positivity) hE]
  exact hBg.trans hbudget

theorem compileCopiedForest_state_bound {n : ℕ} (rows : List (Expression n))
    (hb : ∀ e ∈ rows, e.BoundedWeights) (input : Fin n → ℝ)
    (state : Fin (compileCopiedForest rows).size → ℝ) (X E : ℝ)
    (hX : 0 ≤ X) (hE : 0 ≤ E) (hx : ∀ i, |input i| ≤ X)
    (he : ∀ j, |(compileCopiedForest rows).circuit.residual input state j| ≤ E)
    (j : Fin (compileCopiedForest rows).size) :
    |state j| ≤ (((compileCopiedForest rows).size : ℝ) + 1) * X +
      (((compileCopiedForest rows).size : ℝ) + 1)^2 * E := by
  have h := compileCopiedForest_evaluate_bound rows hb input X E hX hE hx
    ((compileCopiedForest rows).circuit.residual input state) he j
  rwa [(compileCopiedForest rows).circuit.evaluate_residual] at h

/-- Every state coordinate of the actual source compiler is controlled by
the original-input amplitude and the actual complete gate residual. -/
theorem sourceCircuit_state_bound (S : Source.SparseSystem) (precision : ℕ)
    (input : Fin S.n → ℝ) (state : Fin (sourceCircuit S precision).size → ℝ) (X E : ℝ)
    (hX : 0 ≤ X) (hE : 0 ≤ E) (hx : ∀ i, |input i| ≤ X)
    (he : ∀ j, |(sourceCircuit S precision).circuit.residual input state j| ≤ E)
    (j : Fin (sourceCircuit S precision).size) :
    |state j| ≤ (((sourceCircuit S precision).size : ℝ) + 1) * X +
      (((sourceCircuit S precision).size : ℝ) + 1)^2 * E := by
  apply compileCopiedForest_state_bound _ _ input state X E hX hE hx he j
  intro e he
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp he
  exact rowExpression_bounded row

/-- At least two distinct sparse entries force at least two original input
coordinates, all retained by the actual compiler. -/
theorem sourceCircuit_size_two_le (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (precision : ℕ) : 2 ≤ (sourceCircuit S precision).size := by
  have hc := Finset.card_le_card (Finset.subset_univ S.matrix.support)
  have hnnz : S.nnz ≤ S.n * S.n := by
    simpa [Source.SparseSystem.nnz, SparseRationalMatrix.nnz] using hc
  have hn : 2 ≤ S.n := by nlinarith
  exact hn.trans (sourceCircuit S precision).circuit.inputs_le_size

end Maxwell.Logical
