import Maxwell.Logical.RationalCode
import Maxwell.Logical.SourceSquare

namespace Maxwell.Logical.RationalCode

structure Entry where
  row : ℕ
  column : ℕ
  value : ℚ
  deriving DecidableEq

/-- Each allocation prepends its at most three stored coefficients. Thus
the constructor never scans the existing matrix or a dense square. -/
def entries {n d : ℕ} : RationalCode n d → List Entry
  | .input => List.ofFn (fun i : Fin n => ⟨i.val, i.val, 1⟩)
  | @zero _ d c => ⟨d, d, 1⟩ :: c.entries
  | @scale _ d c p w => ⟨d, d, 1⟩ :: ⟨d, p.val, -w⟩ :: c.entries
  | @add _ d c l r => ⟨d, d, 1⟩ :: ⟨d, l.val, -1⟩ :: ⟨d, r.val, -1⟩ :: c.entries

def entrySum (es : List Entry) (i j : ℕ) : ℚ :=
  (es.map (fun e => if e.row = i ∧ e.column = j then e.value else 0)).sum

@[simp] theorem entrySum_cons (e : Entry) (es : List Entry) (i j : ℕ) :
    entrySum (e :: es) i j = (if e.row = i ∧ e.column = j then e.value else 0) + entrySum es i j := rfl

theorem entries_bounded {n d : ℕ} (c : RationalCode n d) (e : Entry) (he : e ∈ c.entries) :
    e.row < d ∧ e.column < d := by
  induction c with
  | input =>
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      exact ⟨i.isLt, i.isLt⟩
  | @zero d c ih =>
      rcases List.mem_cons.mp he with h | h
      · subst e; exact ⟨by simp, by simp⟩
      · obtain ⟨hr, hc⟩ := ih h; exact ⟨by omega, by omega⟩
  | @scale d c p w ih =>
      rcases List.mem_cons.mp he with h | h
      · subst e; exact ⟨by simp, by simp⟩
      · rcases List.mem_cons.mp h with h | h
        · subst e; exact ⟨by simp, Nat.lt_succ_of_lt p.isLt⟩
        · obtain ⟨hr, hc⟩ := ih h; exact ⟨by omega, by omega⟩
  | @add d c l r ih =>
      rcases List.mem_cons.mp he with h | h
      · subst e; exact ⟨by simp, by simp⟩
      · rcases List.mem_cons.mp h with h | h
        · subst e; exact ⟨by simp, Nat.lt_succ_of_lt l.isLt⟩
        · rcases List.mem_cons.mp h with h | h
          · subst e; exact ⟨by simp, Nat.lt_succ_of_lt r.isLt⟩
          · obtain ⟨hr, hc⟩ := ih h; exact ⟨by omega, by omega⟩

theorem entries_length_le {n d : ℕ} (c : RationalCode n d) : c.entries.length ≤ 3 * d := by
  induction c with
  | input => simp only [entries, List.length_ofFn]; omega
  | zero c ih => simp only [entries, List.length_cons]; omega
  | scale c p w ih => simp only [entries, List.length_cons]; omega
  | add c l r ih => simp only [entries, List.length_cons]; omega

theorem entries_length_budget {n d : ℕ} (c : RationalCode n d) :
    c.entries.length + 2 * n ≤ 3 * d := by
  induction c with
  | input => simp only [entries, List.length_ofFn]; omega
  | zero c ih => simp only [entries, List.length_cons]; omega
  | scale c p w ih => simp only [entries, List.length_cons]; omega
  | add c l r ih => simp only [entries, List.length_cons]; omega

theorem entrySum_outside {n d : ℕ} (c : RationalCode n d) (i j : ℕ)
    (h : d ≤ i ∨ d ≤ j) : entrySum c.entries i j = 0 := by
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  have hb := c.entries_bounded e he
  split_ifs with heq
  · omega
  · rfl

@[simp] theorem residual_zero {n d : ℕ} (c : RationalCode n d) (i : Fin d) :
    c.residual (fun _ => 0) i = 0 := by
  induction c with
  | input => rfl
  | zero c ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [residual]
      · simpa only [residual, Fin.snoc_castSucc] using ih j
  | scale c p w ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [residual]
      · simpa only [residual, Fin.snoc_castSucc] using ih j
  | add c l r ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [residual]
      · simpa only [residual, Fin.snoc_castSucc] using ih j

theorem entries_matrix {n d : ℕ} (c : RationalCode n d) (i j : Fin d) :
    entrySum c.entries i.val j.val = c.equationMatrix i j := by
  induction c with
  | input =>
      simp only [entries, entrySum, List.map_ofFn, List.sum_ofFn, equationMatrix, residual]
      change (∑ k : Fin n, if k.val = i.val ∧ k.val = j.val then (1 : ℚ) else 0) = _
      simp only [← Fin.ext_iff, Pi.single_apply]
      by_cases h : i = j
      · subst j; simp
      · have hn (k : Fin n) : ¬(k = i ∧ k = j) := by rintro ⟨rfl, rfl⟩; exact h rfl
        simp only [hn, ↓reduceIte, Finset.sum_const_zero, h]
  | @zero d c ih =>
      refine Fin.lastCases ?_ (fun i' => ?_) i <;>
        refine Fin.lastCases ?_ (fun j' => ?_) j
      · simp [entries, entrySum_cons, c.entrySum_outside d d (Or.inl (le_refl _)),
          equationMatrix, residual]
      · simp [entries, entrySum_cons, c.entrySum_outside d j'.val (Or.inl (le_refl _)),
          equationMatrix, residual, Nat.ne_of_gt j'.isLt]
      · simp [entries, entrySum_cons, c.entrySum_outside i'.val d (Or.inr (le_refl _)),
          equationMatrix, residual, Nat.ne_of_gt i'.isLt]
      · simp only [entries, entrySum_cons, Fin.val_castSucc, Nat.ne_of_gt i'.isLt,
          false_and, ↓reduceIte, zero_add, ih, equationMatrix, residual, Fin.snoc_castSucc]
        congr 1
        funext k
        simp [Pi.single_apply]
  | @scale d c p w ih =>
      refine Fin.lastCases ?_ (fun i' => ?_) i <;>
        refine Fin.lastCases ?_ (fun j' => ?_) j
      · simp [entries, entrySum_cons, c.entrySum_outside d d (Or.inl (le_refl _)),
          equationMatrix, residual, Nat.ne_of_lt p.isLt]
      · simp [entries, entrySum_cons, c.entrySum_outside d j'.val (Or.inl (le_refl _)),
          equationMatrix, residual, Nat.ne_of_gt j'.isLt, Pi.single_apply, Fin.ext_iff]
        split_ifs <;> rfl
      · simp [entries, entrySum_cons, c.entrySum_outside i'.val d (Or.inr (le_refl _)),
          equationMatrix, residual, Nat.ne_of_gt i'.isLt]
      · simp only [entries, entrySum_cons, Fin.val_castSucc, Nat.ne_of_gt i'.isLt,
          false_and, ↓reduceIte, zero_add, ih, equationMatrix, residual, Fin.snoc_castSucc]
        congr 1
        funext k
        simp [Pi.single_apply]
  | @add d c l r ih =>
      refine Fin.lastCases ?_ (fun i' => ?_) i <;>
        refine Fin.lastCases ?_ (fun j' => ?_) j
      · simp [entries, entrySum_cons, c.entrySum_outside d d (Or.inl (le_refl _)),
          equationMatrix, residual, Nat.ne_of_lt l.isLt, Nat.ne_of_lt r.isLt]
      · simp [entries, entrySum_cons, c.entrySum_outside d j'.val (Or.inl (le_refl _)),
          equationMatrix, residual, Nat.ne_of_gt j'.isLt, Pi.single_apply, Fin.ext_iff]
        split_ifs <;> norm_num
      · simp [entries, entrySum_cons, c.entrySum_outside i'.val d (Or.inr (le_refl _)),
          equationMatrix, residual, Nat.ne_of_gt i'.isLt]
      · simp only [entries, entrySum_cons, Fin.val_castSucc, Nat.ne_of_gt i'.isLt,
          false_and, ↓reduceIte, zero_add, ih, equationMatrix, residual, Fin.snoc_castSucc]
        congr 1
        funext k
        simp [Pi.single_apply]

/-- The emitted square system replaces the original boundary rows by the
actual output selectors, in one sparse pass. -/
def squareEntries {n d : ℕ} (c : RationalCode n d) (output : Fin n → Fin d) : List Entry :=
  List.ofFn (fun i : Fin n => ⟨i.val, (output i).val, 1⟩) ++
    c.entries.filter (fun e => decide (n ≤ e.row))

theorem squareEntries_length_le {n d : ℕ} (c : RationalCode n d) (output : Fin n → Fin d) :
    (c.squareEntries output).length ≤ 3 * d := by
  have hfilter := List.length_filter_le (fun e : Entry => decide (n ≤ e.row)) c.entries
  have hb := c.entries_length_budget
  simp only [squareEntries, List.length_append, List.length_ofFn]
  omega

theorem squareEntries_bounded {n d : ℕ} (c : RationalCode n d) (output : Fin n → Fin d)
    (e : Entry) (he : e ∈ c.squareEntries output) : e.row < d ∧ e.column < d := by
  rcases List.mem_append.mp he with h | h
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    exact ⟨i.isLt.trans_le c.realify.inputs_le_size, (output i).isLt⟩
  · exact c.entries_bounded e (List.mem_filter.mp h).1

theorem entrySum_filter_row (es : List Entry) (n i j : ℕ) :
    entrySum (es.filter (fun e => decide (n ≤ e.row))) i j =
      if n ≤ i then entrySum es i j else 0 := by
  induction es with
  | nil => simp [entrySum]
  | cons e es ih =>
      by_cases he : n ≤ e.row <;> by_cases hi : n ≤ i
      · simp [he, hi, ih]
      · have hne : e.row ≠ i := by omega
        simp [he, hi, ih, hne]
      · have hne : e.row ≠ i := by omega
        simp [he, hi, ih, hne]
      · simp [he, hi, ih]

theorem squareEntries_matrix {n d : ℕ} (c : RationalCode n d)
    (output : Fin n → Fin d) (i j : Fin d) :
    entrySum (c.squareEntries output) i.val j.val = c.squareMatrix output i j := by
  have happend (a b : List Entry) : entrySum (a ++ b) i.val j.val =
      entrySum a i.val j.val + entrySum b i.val j.val := by
    simp [entrySum]
  rw [squareEntries, happend, entrySum_filter_row]
  by_cases hi : i.val < n
  · let k : Fin n := ⟨i.val, hi⟩
    simp only [Nat.not_le_of_gt hi, ↓reduceIte, add_zero, squareMatrix, hi, ↓reduceDIte,
      entrySum, List.map_ofFn, List.sum_ofFn]
    change (∑ a : Fin n, if a.val = k.val ∧ (output a).val = j.val then (1 : ℚ) else 0) = _
    simp only [← Fin.ext_iff]
    rw [Finset.sum_eq_single k]
    · simp [k]
    · intro b _ hb
      simp [hb]
    · simp
  · have hn (k : Fin n) : k.val ≠ i.val := by have := k.isLt; omega
    simp only [Nat.le_of_not_gt hi, ↓reduceIte, squareMatrix, hi, ↓reduceDIte]
    have hz : entrySum (List.ofFn (fun k : Fin n => Entry.mk k.val (output k).val 1)) i.val j.val = 0 := by
      simp only [entrySum, List.map_ofFn, List.sum_ofFn]
      change (∑ k : Fin n, if k.val = i.val ∧ (output k).val = j.val then (1 : ℚ) else 0) = 0
      simp [hn]
    rw [hz, zero_add, c.entries_matrix]

end Maxwell.Logical.RationalCode

namespace Maxwell.Logical

def sourceSquareMatrixQ (S : Source.SparseSystem) (precision : ℕ) :
    Matrix (Fin (sourceCircuit S precision).size) (Fin (sourceCircuit S precision).size) ℚ :=
  (sourceCircuit_rational S precision).code.squareMatrix (sourceOutput S precision)

theorem sourceSquareMatrixQ_cast (S : Source.SparseSystem) (precision : ℕ) (i j) :
    (sourceSquareMatrixQ S precision i j : ℝ) = (sourceSquareMap S precision).toMatrix' i j := by
  rw [sourceSquareMatrixQ, RationalCode.squareMatrix_cast, (sourceCircuit_rational S precision).correct]
  rfl

def sourceSquareEntries (S : Source.SparseSystem) (precision : ℕ) : List RationalCode.Entry :=
  (sourceCircuit_rational S precision).code.squareEntries (sourceOutput S precision)

theorem sourceSquareEntries_length_le (S : Source.SparseSystem) (precision : ℕ) :
    (sourceSquareEntries S precision).length ≤ 3 * (sourceCircuit S precision).size :=
  RationalCode.squareEntries_length_le _ _

theorem sourceSquareEntries_matrix (S : Source.SparseSystem) (precision : ℕ) (i j) :
    RationalCode.entrySum (sourceSquareEntries S precision) i.val j.val =
      sourceSquareMatrixQ S precision i j := RationalCode.squareEntries_matrix _ _ _ _

end Maxwell.Logical
