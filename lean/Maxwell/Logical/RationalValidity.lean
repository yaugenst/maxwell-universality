import Maxwell.Logical.RationalSparse
import Maxwell.Logical.Gates

namespace Maxwell.Logical

def RationalCode.Valid {n d : ℕ} : RationalCode n d → Prop
  | .input => True
  | .zero c => c.Valid
  | .scale c _ w => c.Valid ∧ AllowedWeight (w : ℝ)
  | .add c l r => c.Valid ∧ l ≠ r

theorem compileExpression_rational_valid {n d v : ℕ} (e : Expression v)
    (prior : Circuit n d) (ids : Fin v → Fin d) (r : RationalRealization prior)
    (hr : r.code.Valid) (hw : e.FiniteWeights) (hi : e.LinearInputs ids) :
    (compileExpression_rational e prior ids r).code.Valid := by
  induction e generalizing d with
  | var i => exact hr
  | zero => exact hr
  | scale a e ih => exact ⟨ih prior ids r hr hw.2 hi, hw.1⟩
  | add a b iha ihb =>
      let l := compileExpression a prior ids
      let rr := compileExpression b l.circuit (fun i => Fin.castLE l.size_le (ids i))
      let lr := compileExpression_rational a prior ids r
      have ha : a.LinearInputs ids := by intro k; have := hi k; change _ + _ ≤ 1 at this; omega
      have hb : b.LinearInputs ids := by intro k; have := hi k; change _ + _ ≤ 1 at this; omega
      have hl : lr.code.Valid := iha prior ids r hr hw.1 ha
      exact ⟨ihb l.circuit _ lr hl hw.2 (hb.castLE l.size_le), addition_parents_distinct hi l rr⟩

theorem compileForest_rational_valid {n d v : ℕ} (es : List (Expression v))
    (prior : Circuit n d) (ids : Fin v → Fin d) (r : RationalRealization prior)
    (hr : r.code.Valid) (hw : ∀ e ∈ es, e.FiniteWeights)
    (hi : ∀ e ∈ es, e.LinearInputs ids) :
    (compileForest_rational es prior ids r).code.Valid := by
  induction es generalizing d with
  | nil => exact hr
  | cons e es ih =>
      let h := compileExpression e prior ids
      let rh := compileExpression_rational e prior ids r
      have hh : rh.code.Valid := compileExpression_rational_valid e prior ids r hr
        (hw e (by simp)) (hi e (by simp))
      exact ih h.circuit _ rh hh (fun a ha => hw a (by simp [ha]))
        (fun a ha => (hi a (by simp [ha])).castLE h.size_le)

theorem CopyBank.allocate_rational_valid {n : ℕ} (requests : List (Fin n))
    (bank : CopyBank n) (r : RationalRealization bank.circuit) (hr : r.code.Valid) :
    (bank.allocate_rational requests r).code.Valid := by
  induction requests generalizing bank with
  | nil => exact hr
  | cons i requests ih =>
      apply ih
      exact ⟨⟨hr, by norm_num [AllowedWeight]⟩, by norm_num [AllowedWeight]⟩

theorem compileCopiedForest_rational_valid {n : ℕ} (rows : List (Expression n))
    (hw : ∀ e ∈ rows, e.FiniteWeights) : (compileCopiedForest_rational rows).code.Valid := by
  apply compileForest_rational_valid
  · exact CopyBank.allocate_rational_valid _ _ _ trivial
  · exact linearizedRows_finiteWeights rows hw
  · intro e he k
    have hs := linearizedRows_inputUses_le_one rows (copiedForestInputs rows)
      (copiedForestInputs_injective rows) k
    exact (List.single_le_sum (fun _ _ => Nat.zero_le _) _
      (List.mem_map.mpr ⟨e, he, rfl⟩)).trans hs

theorem sourceCircuit_rational_valid (S : Source.SparseSystem) (precision : ℕ) :
    (sourceCircuit_rational S precision).code.Valid := by
  apply compileCopiedForest_rational_valid
  intro e he
  obtain ⟨terms, _, rfl⟩ := List.mem_map.mp he
  exact rowExpression_finiteWeights terms

namespace AllowedWeight

theorem neg {w : ℝ} (h : AllowedWeight w) : AllowedWeight (-w) := by
  rcases h with h | h | h | h <;> rw [h] <;> norm_num [AllowedWeight]

theorem ne_zero {w : ℝ} (h : AllowedWeight w) : w ≠ 0 := by
  rcases h with h | h | h | h <;> rw [h] <;> norm_num

theorem rational {q : ℚ} (h : AllowedWeight (q : ℝ)) : ∃ w : Weight, q = w.value := by
  rcases h with h | h | h | h
  · exact ⟨.one, by norm_num [Weight.value]; exact_mod_cast h⟩
  · exact ⟨.negOne, by norm_num [Weight.value]; exact_mod_cast h⟩
  · refine ⟨.half, ?_⟩
    apply Rat.cast_injective (α := ℝ)
    simpa [Weight.value] using h
  · refine ⟨.negHalf, ?_⟩
    apply Rat.cast_injective (α := ℝ)
    simpa [Weight.value] using h

end AllowedWeight

namespace RationalCode

def Entry.key (e : Entry) : ℕ × ℕ := (e.row, e.column)

theorem Valid.entries_alphabet {n d : ℕ} {c : RationalCode n d} (h : c.Valid)
    (e : Entry) (he : e ∈ c.entries) : AllowedWeight (e.value : ℝ) := by
  induction c with
  | input =>
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      norm_num [AllowedWeight]
  | zero c ih =>
      rcases List.mem_cons.mp he with h' | h'
      · subst e; norm_num [AllowedWeight]
      · exact ih h h'
  | scale c p w ih =>
      rcases List.mem_cons.mp he with h' | h'
      · subst e; norm_num [AllowedWeight]
      · rcases List.mem_cons.mp h' with h' | h'
        · subst e
          simpa only [Rat.cast_neg] using h.2.neg
        · exact ih h.1 h'
  | add c l r ih =>
      rcases List.mem_cons.mp he with h' | h'
      · subst e; norm_num [AllowedWeight]
      · rcases List.mem_cons.mp h' with h' | h'
        · subst e; norm_num [AllowedWeight]
        · rcases List.mem_cons.mp h' with h' | h'
          · subst e; norm_num [AllowedWeight]
          · exact ih h.1 h'

theorem entries_key_old {n d : ℕ} (c : RationalCode n d) (k : ℕ) :
    (d, k) ∉ c.entries.map Entry.key := by
  intro h
  obtain ⟨e, he, hk⟩ := List.mem_map.mp h
  have hb := (c.entries_bounded e he).1
  have hr := congrArg Prod.fst hk
  change e.row = d at hr
  omega

theorem Valid.entries_nodup {n d : ℕ} {c : RationalCode n d} (h : c.Valid) :
    (c.entries.map Entry.key).Nodup := by
  induction c with
  | input =>
      rw [entries, List.map_ofFn]
      apply List.nodup_ofFn.mpr
      intro i j hij
      exact Fin.ext (congrArg Prod.fst hij)
  | @zero d c ih =>
      simp only [entries, List.map_cons, Entry.key, List.nodup_cons]
      exact ⟨c.entries_key_old d, ih h⟩
  | @scale d c p w ih =>
      simp only [entries, List.map_cons, Entry.key, List.nodup_cons, List.mem_cons, not_or]
      refine ⟨⟨?_, c.entries_key_old d⟩, c.entries_key_old p.val, ih h.1⟩
      intro he
      have hv := congrArg Prod.snd he
      have hp := p.isLt
      simp only at hv
      omega
  | @add d c l r ih =>
      simp only [entries, List.map_cons, Entry.key, List.nodup_cons, List.mem_cons, not_or]
      refine ⟨⟨?_, ?_, c.entries_key_old d⟩,
        ⟨?_, c.entries_key_old l.val⟩, c.entries_key_old r.val, ih h.1⟩
      · intro he; have hv := congrArg Prod.snd he; have hl := l.isLt; simp only at hv; omega
      · intro he; have hv := congrArg Prod.snd he; have hr := r.isLt; simp only at hv; omega
      · intro he
        exact h.2 (Fin.ext (congrArg Prod.snd he))

theorem Valid.squareEntries_alphabet {n d : ℕ} {c : RationalCode n d} (h : c.Valid)
    (output : Fin n → Fin d) (e : Entry) (he : e ∈ c.squareEntries output) :
    AllowedWeight (e.value : ℝ) := by
  rcases List.mem_append.mp he with he | he
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    norm_num [AllowedWeight]
  · exact h.entries_alphabet e (List.mem_filter.mp he).1

theorem Valid.squareEntries_nodup {n d : ℕ} {c : RationalCode n d} (h : c.Valid)
    (output : Fin n → Fin d) : ((c.squareEntries output).map Entry.key).Nodup := by
  rw [squareEntries, List.map_append]
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_ofFn]
    apply List.nodup_ofFn.mpr
    intro i j hij
    exact Fin.ext (congrArg Prod.fst hij)
  · exact (List.filter_sublist.map Entry.key).nodup h.entries_nodup
  · intro k hk k' hk' heq
    subst k'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hk'
    have hrow : n ≤ e.row := of_decide_eq_true (List.mem_filter.mp he).2
    have hv := congrArg Prod.fst heq
    change e.row = i.val at hv
    have hi := i.isLt
    omega

end RationalCode

theorem sourceSquareEntries_nodup (S : Source.SparseSystem) (precision : ℕ) :
    ((sourceSquareEntries S precision).map RationalCode.Entry.key).Nodup :=
  (sourceCircuit_rational_valid S precision).squareEntries_nodup _

theorem sourceSquareEntries_alphabet (S : Source.SparseSystem) (precision : ℕ)
    (e : RationalCode.Entry) (he : e ∈ sourceSquareEntries S precision) :
    ∃ w : Weight, e.value = w.value :=
  ((sourceCircuit_rational_valid S precision).squareEntries_alphabet _ e he).rational

theorem sourceSquareEntries_nonzero (S : Source.SparseSystem) (precision : ℕ)
    (e : RationalCode.Entry) (he : e ∈ sourceSquareEntries S precision) : e.value ≠ 0 := by
  obtain ⟨w, hw⟩ := sourceSquareEntries_alphabet S precision e he
  rw [hw]
  exact w.ne_zero

end Maxwell.Logical
