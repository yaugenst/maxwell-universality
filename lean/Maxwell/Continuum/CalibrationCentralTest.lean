import Maxwell.Continuum.CalibrationRawCoefficientTable

/-! A nonnegative rational polynomial decides whether an alias is one of
the eight central aliases. It gives the exact branch condition for the
runtime free-block evaluator. -/

namespace Maxwell.Continuum.Calibration.RawFree

open RationalDataflow FreeFiber
set_option maxHeartbeats 2000000

def centralMetric (c : Fin 3 → Parts) : Parts :=
  sumThree (fun j =>
    let x := (c j).mul ((c j).add (Parts.literal 1))
    x.mul x)

theorem centralMetric_valid (c : Fin 3 → Parts) (hc : ∀ j, (c j).Valid) :
    (centralMetric c).Valid := by
  apply sumThree_valid
  intro j
  have h := Parts.mul_valid (hc j) (Parts.add_valid (hc j) (Parts.literal_valid 1))
  exact Parts.mul_valid h h

theorem centralMetric_value (c : Fin 3 → Parts) (hc : ∀ j, (c j).Valid) :
    (centralMetric c).value=∑ j, ((c j).value*((c j).value+1))^2 := by
  unfold centralMetric
  rw [sumThree_value _ (fun j => Parts.mul_valid
    (Parts.mul_valid (hc j) (Parts.add_valid (hc j) (Parts.literal_valid 1)))
    (Parts.mul_valid (hc j) (Parts.add_valid (hc j) (Parts.literal_valid 1))))]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Parts.mul_value,Parts.add_value _ _ (hc j) (Parts.literal_valid 1),Parts.literal_value]
  ring

theorem centralMetric_nonneg (c : Fin 3 → Parts) (hc : ∀ j, (c j).Valid) :
    0 ≤ (centralMetric c).value := by
  rw [centralMetric_value c hc]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem centralMetric_eq_zero (c : Fin 3 → Parts) (hc : ∀ j, (c j).Valid)
    (ν : Alias) (hν : ∀ j, (c j).value=(ν j : ℚ)) :
    (centralMetric c).value=0 ↔ IsCentralAlias ν := by
  rw [centralMetric_value c hc]
  simp_rw [hν]
  constructor
  · intro h j
    have hj := Finset.single_le_sum (fun k (_ : k∈Finset.univ) =>
      sq_nonneg ((ν k : ℚ)*((ν k : ℚ)+1))) (Finset.mem_univ j)
    rw [h] at hj
    have hz : ((ν j : ℚ)*((ν j : ℚ)+1))^2=0 := le_antisymm hj (sq_nonneg _)
    rcases mul_eq_zero.mp (sq_eq_zero_iff.mp hz) with hz | hz
    · exact Or.inr (by exact_mod_cast hz)
    · left
      have he : (ν j : ℚ) = -1 := by linarith
      exact_mod_cast he
  · intro h
    apply Finset.sum_eq_zero
    intro j _
    rcases h j with hj | hj <;> simp [hj]

theorem centralMetric_pos (c : Fin 3 → Parts) (hc : ∀ j, (c j).Valid)
    (ν : Alias) (hν : ∀ j, (c j).value=(ν j : ℚ)) :
    0 < (centralMetric c).value ↔ ¬IsCentralAlias ν := by
  have hn := centralMetric_nonneg c hc
  have hz := centralMetric_eq_zero c hc ν hν
  constructor
  · intro hp hcentral
    have he := hz.mpr hcentral
    linarith
  · intro hnot
    have he : (centralMetric c).value ≠ 0 := fun h => hnot (hz.mp h)
    exact lt_of_le_of_ne hn he.symm

#print axioms centralMetric_pos

end Maxwell.Continuum.Calibration.RawFree
