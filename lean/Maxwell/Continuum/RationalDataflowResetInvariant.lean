import Maxwell.Continuum.RationalDataflowResetList

/-! Resetting temporary registers restores a width bound determined only
by retained inputs. This avoids an artificial width recurrence in loops. -/
namespace Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 1500000

theorem resetList_result_width (S : Finset ℕ) (xs : List ℕ) (v : ℕ→Parts) (B : ℕ)
    (hB : 1 ≤ B) (hv : ∀i∈S,i∉xs→(v i).Width B) :
    WidthBank S B ((resetList xs).evaluate v) := by
  intro i hi
  rw [resetList_values]
  by_cases hx : i∈xs
  · rw [ite_eq_left hx]
    exact (show (Parts.literal 0).Width 1 by
      norm_num [Parts.literal,Parts.Width]).mono hB
  · rw [ite_eq_right hx]
    exact hv i hi hx

theorem resetList_result_good (S : Finset ℕ) (xs : List ℕ) (v : ℕ→Parts)
    (hv : ∀i∈S,i∉xs→(v i).Valid) : Good S ((resetList xs).evaluate v) := by
  intro i hi
  rw [resetList_values]
  by_cases hx : i∈xs
  · rw [ite_eq_left hx]
    exact Parts.literal_valid 0
  · rw [ite_eq_right hx]
    exact hv i hi hx

theorem resetList_congr (xs : List ℕ) (v w : ℕ→Parts) (h : ∀i,i∉xs→v i=w i) :
    (resetList xs).evaluate v=(resetList xs).evaluate w := by
  funext i
  simp only [resetList_values]
  by_cases hx : i∈xs <;> simp [hx,h i]

#print axioms resetList_result_width
end Maxwell.Continuum.RationalDataflow
