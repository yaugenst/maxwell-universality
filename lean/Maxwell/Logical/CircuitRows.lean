import Maxwell.Logical.CompilerAlphabet
import Maxwell.Composition.CircuitColumns

/-! Row support and coefficient bounds for the actual compiled matrices. -/

noncomputable section

namespace Maxwell.Logical

open Maxwell.Composition Maxwell.Composition.CircuitColumns
open scoped BigOperators

theorem AllowedWeight.neg {w : ℝ} (h : AllowedWeight w) : AllowedWeight (-w) := by
  rcases h with rfl | rfl | rfl | rfl <;> norm_num [AllowedWeight]

namespace Circuit

theorem rowSupport_card_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (i : ι) :
    (PositiveEdges.rowSupport H i).card = ∑ j, if H i j = 0 then 0 else 1 := by
  classical
  simp [PositiveEdges.rowSupport, Finset.card_filter, ite_not]

theorem append_rowSupport_le_three {n d : ℕ} (c : Circuit n d) (a : Fin d → ℝ)
    (hc : ∀ i, (PositiveEdges.rowSupport c.equationMatrix i).card ≤ 3)
    (ha : (Finset.univ.filter fun j => a j ≠ 0).card ≤ 2) :
    ∀ i, (PositiveEdges.rowSupport (c.append a).equationMatrix i).card ≤ 3 := by
  classical
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [rowSupport_card_eq_sum, Fin.sum_univ_castSucc]
    simp only [equationMatrix_append_last_old, neg_eq_zero,
      equationMatrix_append_last_last, one_ne_zero, ite_false]
    have hh : (∑ j, if a j = 0 then 0 else 1 : ℕ) ≤ 2 := by
      simpa only [Finset.card_filter, ite_not] using ha
    omega
  · rw [rowSupport_card_eq_sum, Fin.sum_univ_castSucc]
    simpa only [equationMatrix_append_old_old, equationMatrix_append_old_last,
      ite_true, Nat.add_zero, ← rowSupport_card_eq_sum] using hc k

theorem SmallGates.equationMatrix_rowSupport_le_three {n d : ℕ} {c : Circuit n d}
    (h : c.SmallGates) : ∀ i, (PositiveEdges.rowSupport c.equationMatrix i).card ≤ 3 := by
  classical
  induction h with
  | input =>
      intro i
      simp [rowSupport_card_eq_sum, equationMatrix_entry, residual, Pi.single_apply]
  | @zero d c _ ih =>
      apply append_rowSupport_le_three c 0 ih
      simp
  | @scale d c _ parent weight _ ih =>
      apply append_rowSupport_le_three c _ ih
      have hs : (Finset.univ.filter fun j : Fin d =>
          (if j = parent then weight else 0) ≠ 0) ⊆ {parent} := by
        intro j hj
        by_contra hn
        simp only [Finset.mem_singleton] at hn
        simp [hn] at hj
      exact (Finset.card_le_card hs).trans (by simp)
  | @add d c _ left right _ ih =>
      apply append_rowSupport_le_three c _ ih
      have hs : (Finset.univ.filter fun j : Fin d =>
          (if j = left then (1 : ℝ) else 0) + (if j = right then 1 else 0) ≠ 0) ⊆
          {left, right} := by
        intro j hj
        by_contra hn
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
        simp [hn.1, hn.2] at hj
      exact (Finset.card_le_card hs).trans (by
        simpa using Finset.card_insert_le left ({right} : Finset (Fin d)))

theorem append_equationMatrix_alphabet {n d : ℕ} (c : Circuit n d) (a : Fin d → ℝ)
    (hc : ∀ i j, c.equationMatrix i j = 0 ∨ AllowedWeight (c.equationMatrix i j))
    (ha : ∀ j, a j = 0 ∨ AllowedWeight (a j)) :
    ∀ i j, (c.append a).equationMatrix i j = 0 ∨
      AllowedWeight ((c.append a).equationMatrix i j) := by
  intro i j
  refine Fin.lastCases ?_ (fun k => ?_) i
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · rw [equationMatrix_append_last_last]
      exact Or.inr (Or.inl rfl)
    · rw [equationMatrix_append_last_old]
      rcases ha l with hz | hw
      · exact Or.inl (by simp [hz])
      · exact Or.inr hw.neg
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · rw [equationMatrix_append_old_last]
      exact Or.inl rfl
    · rw [equationMatrix_append_old_old]
      exact hc k l

theorem SmallGates.equationMatrix_alphabet {n d : ℕ} {c : Circuit n d}
    (h : c.SmallGates) :
    ∀ i j, c.equationMatrix i j = 0 ∨ AllowedWeight (c.equationMatrix i j) := by
  induction h with
  | input =>
      intro i j
      by_cases hij : i = j <;>
        simp [equationMatrix_entry, residual, hij, AllowedWeight]
  | @zero d c _ ih =>
      exact append_equationMatrix_alphabet c 0 ih (fun _ => Or.inl rfl)
  | @scale d c _ parent weight hw ih =>
      apply append_equationMatrix_alphabet c _ ih
      intro j
      by_cases hj : j = parent
      · exact Or.inr (by simpa [hj] using hw)
      · exact Or.inl (by simp [hj])
  | @add d c _ left right hne ih =>
      apply append_equationMatrix_alphabet c _ ih
      intro j
      by_cases hl : j = left
      · subst j
        simp [hne, AllowedWeight]
      · by_cases hr : j = right
        · subst j
          simp [hl, AllowedWeight]
        · simp [hl, hr]

theorem squareMap_rowSupport_le_three {n d : ℕ} (c : Circuit n d)
    (output : Fin n → Fin d)
    (hc : ∀ i, (PositiveEdges.rowSupport c.equationMatrix i).card ≤ 3) (i : Fin d) :
    (PositiveEdges.rowSupport (c.squareMap output).toMatrix' i).card ≤ 3 := by
  classical
  by_cases hin : i.val < n
  · let k : Fin n := ⟨i.val, hin⟩
    have hk : c.inputIndex k = i := Fin.ext (c.inputIndex_value k)
    have he (j : Fin d) : (c.squareMap output).toMatrix' i j =
        (Pi.single j (1 : ℝ) : Fin d → ℝ) (output k) := by
      rw [LinearMap.toMatrix'_apply, ← hk, c.squareMap_input]
    have hs : PositiveEdges.rowSupport (c.squareMap output).toMatrix' i ⊆ {output k} := by
      intro j hj
      have hn := (Finset.mem_filter.mp hj).2
      by_contra hj'
      simp only [Finset.mem_singleton] at hj'
      exact hn (by simp [he, Ne.symm hj'])
    exact (Finset.card_le_card hs).trans (by simp)
  · have he : PositiveEdges.rowSupport (c.squareMap output).toMatrix' i =
        PositiveEdges.rowSupport c.equationMatrix i := by
      have hentry (j : Fin d) : (c.squareMap output).toMatrix' i j = c.equationMatrix i j := by
        rw [LinearMap.toMatrix'_apply,
          c.squareMap_noninput output (Pi.single j 1) i (Nat.le_of_not_gt hin)]
        rfl
      simp only [PositiveEdges.rowSupport, hentry]
    rw [he]
    exact hc i

theorem squareMap_alphabet {n d : ℕ} (c : Circuit n d) (output : Fin n → Fin d)
    (hc : ∀ i j, c.equationMatrix i j = 0 ∨ AllowedWeight (c.equationMatrix i j)) :
    ∀ i j, (c.squareMap output).toMatrix' i j = 0 ∨
      AllowedWeight ((c.squareMap output).toMatrix' i j) := by
  intro i j
  by_cases hin : i.val < n
  · let k : Fin n := ⟨i.val, hin⟩
    have hk : c.inputIndex k = i := Fin.ext (c.inputIndex_value k)
    rw [LinearMap.toMatrix'_apply, ← hk, c.squareMap_input]
    by_cases hj : output k = j <;> simp [hj, AllowedWeight]
  · simpa only [LinearMap.toMatrix'_apply,
      c.squareMap_noninput output (Pi.single j 1) i (Nat.le_of_not_gt hin),
      ← equationMatrix_entry] using hc i j

theorem SmallGates.squareMap_rowSupport_le_three {n d : ℕ} {c : Circuit n d}
    (h : c.SmallGates) (output : Fin n → Fin d) (i : Fin d) :
    (PositiveEdges.rowSupport (c.squareMap output).toMatrix' i).card ≤ 3 :=
  c.squareMap_rowSupport_le_three output h.equationMatrix_rowSupport_le_three i

theorem SmallGates.squareMap_alphabet {n d : ℕ} {c : Circuit n d}
    (h : c.SmallGates) (output : Fin n → Fin d) (i j : Fin d) :
    (c.squareMap output).toMatrix' i j = 0 ∨
      AllowedWeight ((c.squareMap output).toMatrix' i j) :=
  c.squareMap_alphabet output h.equationMatrix_alphabet i j

end Circuit

end Maxwell.Logical
