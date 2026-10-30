import Maxwell.Continuum.CalibrationCentralTest
import Maxwell.Continuum.CalibrationStencilEntryFactor

/-! Exact rational squared-distance tests for the six actual Fourier
neighbors, including negative and central alias coordinates. -/

namespace Maxwell.Continuum.Calibration.RawFree

open RationalDataflow FreeFiber
set_option maxHeartbeats 2500000

def neighborOffset (d : Fin 3) (plus : Bool) (k : Fin 3) : ℚ :=
  if k=d then (if plus then 1 else -1) else 0

def shiftedAlias (ν : Alias) (d : Fin 3) (plus : Bool) : Alias :=
  if plus then ν+unitAlias d else ν-unitAlias d

theorem shiftedAlias_cast (ν : Alias) (d : Fin 3) (plus : Bool) (k : Fin 3) :
    (shiftedAlias ν d plus k : ℚ)=(ν k : ℚ)+neighborOffset d plus k := by
  cases plus <;> by_cases hk : k=d <;>
    simp [shiftedAlias,neighborOffset,unitAlias,hk,sub_eq_add_neg]

def neighborDifference (c m : Fin 3 → Parts) (d : Fin 3) (plus : Bool) (k : Fin 3) : Parts :=
  ((c k).add (Parts.literal (neighborOffset d plus k))).sub (m k)

def neighborMetric (c m : Fin 3 → Parts) (d : Fin 3) (plus : Bool) : Parts :=
  sumThree (fun k => let x := neighborDifference c m d plus k; x.mul x)

theorem neighborDifference_valid (c m : Fin 3 → Parts) (d : Fin 3) (plus : Bool)
    (hc : ∀ k, (c k).Valid) (hm : ∀ k, (m k).Valid) (k : Fin 3) :
    (neighborDifference c m d plus k).Valid :=
  Parts.sub_valid (Parts.add_valid (hc k) (Parts.literal_valid _)) (hm k)

theorem neighborDifference_value (c m : Fin 3 → Parts) (d : Fin 3) (plus : Bool)
    (hc : ∀ k, (c k).Valid) (hm : ∀ k, (m k).Valid) (k : Fin 3) :
    (neighborDifference c m d plus k).value=(c k).value+neighborOffset d plus k-(m k).value := by
  rw [neighborDifference,Parts.sub_value _ _ (Parts.add_valid (hc k) (Parts.literal_valid _)) (hm k),
    Parts.add_value _ _ (hc k) (Parts.literal_valid _),Parts.literal_value]

theorem neighborMetric_valid (c m : Fin 3 → Parts) (d : Fin 3) (plus : Bool)
    (hc : ∀ k, (c k).Valid) (hm : ∀ k, (m k).Valid) : (neighborMetric c m d plus).Valid :=
  sumThree_valid _ (fun k => Parts.mul_valid (neighborDifference_valid c m d plus hc hm k)
    (neighborDifference_valid c m d plus hc hm k))

theorem neighborMetric_value (c m : Fin 3 → Parts) (d : Fin 3) (plus : Bool)
    (hc : ∀ k, (c k).Valid) (hm : ∀ k, (m k).Valid) :
    (neighborMetric c m d plus).value=
      ∑ k, ((c k).value+neighborOffset d plus k-(m k).value)^2 := by
  rw [neighborMetric,sumThree_value _ (fun k => Parts.mul_valid
    (neighborDifference_valid c m d plus hc hm k) (neighborDifference_valid c m d plus hc hm k))]
  simp only [Parts.mul_value,neighborDifference_value c m d plus hc hm,pow_two]

theorem neighborMetric_nonneg (c m : Fin 3 → Parts) (d : Fin 3) (plus : Bool)
    (hc : ∀ k, (c k).Valid) (hm : ∀ k, (m k).Valid) : 0≤(neighborMetric c m d plus).value := by
  rw [neighborMetric_value c m d plus hc hm]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem neighborMetric_eq_zero (c m : Fin 3 → Parts) (d : Fin 3) (plus : Bool)
    (hc : ∀ k, (c k).Valid) (hm : ∀ k, (m k).Valid) (ν μ : Alias)
    (hν : ∀ k, (c k).value=(ν k : ℚ)) (hμ : ∀ k, (m k).value=(μ k : ℚ)) :
    (neighborMetric c m d plus).value=0 ↔ shiftedAlias ν d plus=μ := by
  rw [neighborMetric_value c m d plus hc hm]
  simp_rw [hν,hμ,← shiftedAlias_cast]
  constructor
  · intro h
    funext k
    have hk := Finset.single_le_sum (fun l (_ : l∈Finset.univ) =>
      sq_nonneg ((shiftedAlias ν d plus l : ℚ)-(μ l : ℚ))) (Finset.mem_univ k)
    rw [h] at hk
    have hz := sq_eq_zero_iff.mp (le_antisymm hk (sq_nonneg _))
    exact_mod_cast sub_eq_zero.mp hz
  · intro h
    simp [h]

theorem neighborMetric_pos (c m : Fin 3 → Parts) (d : Fin 3) (plus : Bool)
    (hc : ∀ k, (c k).Valid) (hm : ∀ k, (m k).Valid) (ν μ : Alias)
    (hν : ∀ k, (c k).value=(ν k : ℚ)) (hμ : ∀ k, (m k).value=(μ k : ℚ)) :
    0<(neighborMetric c m d plus).value ↔ shiftedAlias ν d plus≠μ := by
  have hn := neighborMetric_nonneg c m d plus hc hm
  have hz := neighborMetric_eq_zero c m d plus hc hm ν μ hν hμ
  constructor
  · intro hp he
    have := hz.mpr he
    linarith
  · intro he
    exact lt_of_le_of_ne hn (fun h => he (hz.mp h.symm))

#print axioms neighborMetric_pos

end Maxwell.Continuum.Calibration.RawFree
