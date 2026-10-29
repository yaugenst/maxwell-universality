import Maxwell.Logical.CopiedForest
import Maxwell.Logical.ForestResidual

namespace Maxwell.Logical

theorem copiedForest_leaf_error {n : ℕ} (rows : List (Expression n))
    (input : Fin n → ℝ) (state : Fin (compileCopiedForest rows).size → ℝ)
    (E : ℝ) (he : ∀ j, |(compileCopiedForest rows).circuit.residual input state j| ≤ E)
    (i : Fin (forestLeafCount rows)) :
    |state (Fin.castLE (compileCopiedForest rows).size_le (copiedForestInputs rows i)) -
      input (forestSources rows i)| ≤ ((forestCopies rows).bank.size : ℝ) * E := by
  let result := compileCopiedForest rows
  let bank := (forestCopies rows).bank
  let oldState : Fin bank.size → ℝ := fun j => state (Fin.castLE result.size_le j)
  have h := bank.copy_only.arbitrary_residual input oldState (copiedForestInputs rows i)
  rw [copiedForestInputs_correct] at h
  calc
    _ ≤ ∑ j, |bank.circuit.residual input oldState j| := h
    _ ≤ ∑ _j : Fin bank.size, E := by
      apply Finset.sum_le_sum
      intro j _
      rw [← result.extension.residual_old input state j]
      exact he _
    _ = _ := by simp [bank]

/-- Every row of the implemented copy-plus-arithmetic circuit has a
polynomial error bound for arbitrary assignments to all auxiliary variables.
The right-hand list consists of the original expressions on the original
input, not a hypothesized logical realization. -/
theorem compileCopiedForest_arbitrary_residual {n : ℕ} (rows : List (Expression n))
    (hb : ∀ e ∈ rows, e.BoundedWeights) (input : Fin n → ℝ)
    (state : Fin (compileCopiedForest rows).size → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (he : ∀ j, |(compileCopiedForest rows).circuit.residual input state j| ≤ E) :
    List.Forall₂ (fun output value => |state output - value| ≤
      (((compileCopiedForest rows).size : ℝ) + 1) ^ 2 * E)
      (compileCopiedForest rows).outputs (rows.map (fun e => e.evaluate input)) := by
  let result := compileCopiedForest rows
  have hbl := linearizedRows_bounded rows hb
  have hraw := result.arbitrary_residual hbl input state E hE he
  have hfinal : List.Forall₂ (fun output e =>
      |state output - e.evaluate (fun i => input (forestSources rows i))| ≤
        ((result.size : ℝ) + 1) ^ 2 * E) result.outputs (linearizedRows rows) := by
    apply forall₂_imp_right_mem hraw
    intro output e hem hrow
    have hl := e.evaluate_lipschitz (hbl e hem)
      (fun i => state (Fin.castLE result.size_le (copiedForestInputs rows i)))
      (fun i => input (forestSources rows i)) (((forestCopies rows).bank.size : ℝ) * E)
      (fun i => copiedForest_leaf_error rows input state E he i)
    have hg : e.gateCount ≤ result.size := by
      have hm : e.gateCount ∈ (linearizedRows rows).map Expression.gateCount :=
        List.mem_map.mpr ⟨e, hem, rfl⟩
      have hs := List.le_sum_of_mem hm
      have ha := result.allocation
      omega
    have hleaf : e.leafCount ≤ result.size + 1 := e.leafCount_le_gateCount_add_one.trans (by omega)
    have hbank : (forestCopies rows).bank.size ≤ result.size := result.size_le
    have hgr : (e.gateCount : ℝ) ≤ result.size := by exact_mod_cast hg
    have hlr : (e.leafCount : ℝ) ≤ (result.size : ℝ) + 1 := by exact_mod_cast hleaf
    have hbr : ((forestCopies rows).bank.size : ℝ) ≤ result.size := by exact_mod_cast hbank
    calc
      _ ≤ |state output - e.evaluate (fun i => state (Fin.castLE result.size_le
            (copiedForestInputs rows i)))| +
          |e.evaluate (fun i => state (Fin.castLE result.size_le (copiedForestInputs rows i))) -
            e.evaluate (fun i => input (forestSources rows i))| := abs_sub_le _ _ _
      _ ≤ (e.gateCount : ℝ) * E + (e.leafCount : ℝ) *
          (((forestCopies rows).bank.size : ℝ) * E) := add_le_add hrow hl
      _ ≤ _ := by
        have hmul : (e.leafCount : ℝ) * ((forestCopies rows).bank.size : ℝ) ≤
            ((result.size : ℝ) + 1) * result.size :=
          mul_le_mul hlr hbr (by positivity) (by positivity)
        nlinarith [mul_le_mul_of_nonneg_right hmul hE,
          mul_le_mul_of_nonneg_right hgr hE]
  have hmap : List.Forall₂ (fun output value => |state output - value| ≤
      ((result.size : ℝ) + 1) ^ 2 * E) result.outputs
      ((linearizedRows rows).map (fun e => e.evaluate (fun i => input (forestSources rows i)))) :=
    (List.forall₂_map_right_iff).2 hfinal
  rw [linearizedRows_evaluate] at hmap
  exact hmap

end Maxwell.Logical
