import Maxwell.Composition.PositiveEdges
import Maxwell.Logical.Forest
import Maxwell.Logical.SquareSystem

/-! Actual matrix column support is bounded by the circuit's charged fanout.
The equation diagonal contributes one; replacing input equations by output
constraints contributes exactly the already charged output incidences. -/

noncomputable section

namespace Maxwell.Composition.CircuitColumns

open Maxwell.Logical
open scoped BigOperators

theorem equationMatrix_entry {n d : ℕ} (c : Circuit n d) (i j : Fin d) :
    c.equationMatrix i j = c.residual 0 (Pi.single j 1) i := rfl

theorem equationMatrix_append_old_old {n d : ℕ} (c : Circuit n d)
    (a : Fin d → ℝ) (i j : Fin d) :
    (c.append a).equationMatrix i.castSucc j.castSucc = c.equationMatrix i j := by
  rw [equationMatrix_entry, equationMatrix_entry]
  simp only [Circuit.residual, Fin.snoc_castSucc]
  congr 2
  funext k
  simp [Pi.single_apply]

theorem equationMatrix_append_last_old {n d : ℕ} (c : Circuit n d)
    (a : Fin d → ℝ) (j : Fin d) :
    (c.append a).equationMatrix (Fin.last d) j.castSucc = -a j := by
  rw [equationMatrix_entry]
  simp [Circuit.residual, Pi.single_apply]

theorem equationMatrix_append_old_last {n d : ℕ} (c : Circuit n d)
    (a : Fin d → ℝ) (i : Fin d) :
    (c.append a).equationMatrix i.castSucc (Fin.last d) = 0 := by
  rw [equationMatrix_entry]
  simp only [Circuit.residual, Fin.snoc_castSucc]
  have hzero : (fun k : Fin d => (Pi.single (Fin.last d) (1 : ℝ) :
      Fin (d + 1) → ℝ) k.castSucc) = 0 := by
    funext k
    simp
  rw [hzero]
  exact congrFun (map_zero c.equationMap) i

theorem equationMatrix_append_last_last {n d : ℕ} (c : Circuit n d)
    (a : Fin d → ℝ) :
    (c.append a).equationMatrix (Fin.last d) (Fin.last d) = 1 := by
  rw [equationMatrix_entry]
  simp [Circuit.residual]

theorem equationMatrix_column_sum {n d : ℕ} (c : Circuit n d) (j : Fin d) :
    (∑ i, if c.equationMatrix i j = 0 then 0 else 1 : ℕ) = c.uses j + 1 := by
  induction c with
  | input =>
    simp [equationMatrix_entry, Circuit.residual, Pi.single_apply]
  | @append d c a ih =>
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [Fin.sum_univ_castSucc, equationMatrix_append_old_last,
        equationMatrix_append_last_last]
    · rw [Fin.sum_univ_castSucc]
      simp only [equationMatrix_append_old_old, equationMatrix_append_last_old,
        neg_eq_zero, ih, Circuit.uses_append_old]
      omega

theorem columnSupport_card_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (j : ι) :
    (PositiveEdges.columnSupport H j).card =
      ∑ i, if H i j = 0 then 0 else 1 := by
  classical
  simp [PositiveEdges.columnSupport, Finset.card_filter, ite_not]

/-- Every equation column contains its diagonal and precisely its downstream uses. -/
theorem equationMatrix_columnSupport_card {n d : ℕ} (c : Circuit n d) (j : Fin d) :
    (PositiveEdges.columnSupport c.equationMatrix j).card = c.uses j + 1 := by
  rw [columnSupport_card_eq_sum, equationMatrix_column_sum]

theorem squareMap_columnSupport_subset {n d : ℕ} (c : Circuit n d)
    (output : Fin n → Fin d) (j : Fin d) :
    PositiveEdges.columnSupport (c.squareMap output).toMatrix' j ⊆
      PositiveEdges.columnSupport c.equationMatrix j ∪
        (Finset.univ.filter (fun i => output i = j)).image c.inputIndex := by
  classical
  intro i hi
  have hn : (c.squareMap output).toMatrix' i j ≠ 0 :=
    (Finset.mem_filter.mp hi).2
  by_cases hin : i.val < n
  · let k : Fin n := ⟨i.val, hin⟩
    have hk : c.inputIndex k = i := Fin.ext (c.inputIndex_value k)
    have hentry : (c.squareMap output).toMatrix' i j =
        (Pi.single j (1 : ℝ) : Fin d → ℝ) (output k) := by
      rw [LinearMap.toMatrix'_apply, ← hk, c.squareMap_input]
    have hout : output k = j := by
      by_contra h
      exact hn (by simp [hentry, h])
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hout⟩, hk⟩
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [LinearMap.toMatrix'_apply,
      c.squareMap_noninput output (Pi.single j 1) i (Nat.le_of_not_gt hin),
      ← equationMatrix_entry] using hn

theorem squareMap_columnSupport_card_le {n d : ℕ} (c : Circuit n d)
    (output : Fin n → Fin d) (j : Fin d) :
    (PositiveEdges.columnSupport (c.squareMap output).toMatrix' j).card ≤
      c.uses j + (∑ i, Circuit.hit j (output i)) + 1 := by
  classical
  calc
    _ ≤ (PositiveEdges.columnSupport c.equationMatrix j ∪
        (Finset.univ.filter (fun i => output i = j)).image c.inputIndex).card :=
      Finset.card_le_card (squareMap_columnSupport_subset c output j)
    _ ≤ (PositiveEdges.columnSupport c.equationMatrix j).card +
        ((Finset.univ.filter (fun i => output i = j)).image c.inputIndex).card :=
      Finset.card_union_le _ _
    _ ≤ (c.uses j + 1) + (Finset.univ.filter (fun i => output i = j)).card := by
      rw [equationMatrix_columnSupport_card]
      exact Nat.add_le_add_left Finset.card_image_le _
    _ = _ := by
      simp only [Finset.card_filter, Circuit.hit, eq_comm]
      omega

theorem squareMap_columnSupport_card_le_chargedList {n d : ℕ} (c : Circuit n d)
    (output : Fin n → Fin d) (j : Fin d) :
    (PositiveEdges.columnSupport (c.squareMap output).toMatrix' j).card ≤
      c.chargedList (List.ofFn output) j + 1 := by
  simpa [Circuit.chargedList, List.map_ofFn, List.sum_ofFn] using
    squareMap_columnSupport_card_le c output j

/-- The compiler's charged fanout bound gives the actual column-degree bound. -/
theorem squareMap_columnSupport_le_three {n d : ℕ} (c : Circuit n d)
    (output : Fin n → Fin d)
    (hcharged : ∀ j, c.chargedList (List.ofFn output) j ≤ 2) (j : Fin d) :
    (PositiveEdges.columnSupport (c.squareMap output).toMatrix' j).card ≤ 3 := by
  have h := squareMap_columnSupport_card_le_chargedList c output j
  have hc := hcharged j
  omega

end Maxwell.Composition.CircuitColumns
