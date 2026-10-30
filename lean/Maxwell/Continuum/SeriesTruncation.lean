import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-! Finite truncation of an absolutely summable series, retaining its full tail. -/

noncomputable section

namespace Maxwell.Continuum

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem series_truncation_norm (f : ℕ → E) (u : ℕ → ℝ) (hu : Summable u)
    (hf : ∀ j, ‖f j‖ ≤ u j) (D : ℕ) :
    ‖(∑' j, f j)-∑ j ∈ Finset.range D, f j‖ ≤ ∑' j, if D ≤ j then u j else 0 := by
  have hs : Summable f := Summable.of_norm_bounded hu hf
  have hp : Summable (fun j => if j < D then f j else 0) := by
    convert hs.indicator {j | j < D} using 1
    funext j
    simp [Set.indicator_apply]
  have ht : Summable (fun j => if D ≤ j then f j else 0) := by
    convert hs.indicator {j | D ≤ j} using 1
    funext j
    simp [Set.indicator_apply]
  have hup : Summable (fun j => if D ≤ j then u j else 0) := by
    convert hu.indicator {j | D ≤ j} using 1
    funext j
    simp [Set.indicator_apply]
  have htail (j : ℕ) : ‖if D ≤ j then f j else 0‖ ≤ (if D ≤ j then u j else 0) := by
    split_ifs <;> simp [hf]
  have htn : Summable (fun j => ‖if D ≤ j then f j else 0‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htail hup
  have he : (∑' j, f j) = (∑' j, if j < D then f j else 0)+(∑' j, if D ≤ j then f j else 0) := by
    rw [← hp.tsum_add ht]
    apply tsum_congr
    intro j
    by_cases hj : j < D
    · simp [hj, Nat.not_le.mpr hj]
    · simp [hj, Nat.le_of_not_gt hj]
  have hfin : (∑' j, if j < D then f j else 0) = ∑ j ∈ Finset.range D, f j := by
    rw [tsum_eq_sum (s := Finset.range D) (by
      intro j hj
      exact ite_eq_right (show ¬ j < D from fun h => hj (Finset.mem_range.mpr h)))]
    apply Finset.sum_congr rfl
    intro j hj
    exact ite_eq_left (Finset.mem_range.mp hj)
  rw [he, hfin, add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm htn).trans (Summable.tsum_le_tsum htail htn hup)

end Maxwell.Continuum
