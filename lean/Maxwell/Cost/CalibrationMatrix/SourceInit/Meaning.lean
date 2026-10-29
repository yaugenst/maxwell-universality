import Maxwell.Cost.CalibrationMatrix.SourceInit.Execute
import Maxwell.Green.CalibrationInteger

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

open Defect.FiniteStencil
open Spectral.Lattice
open scoped BigOperators

/-- Sparse entries are cleared individually. Duplicate edges may contribute
to both output channels; their signed sum is exactly the physical source. -/
theorem values_scaled {m n : ℕ} (r : Records m n) (Q : Fin n ↪ Edge)
    (a : Fin m → ℚ) (V : ℕ)
    (hclear : ∀ j, (((r.positive j : ℤ)-r.negative j : ℤ) : ℚ) = (V : ℚ)*a j)
    (i : Fin n) :
    ((values r m).value i : ℚ) = (V : ℚ)*
      coefficients Q (rationalSource (fun j => Q (r.index j)) a) i := by
  rw [values_full]
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero, coefficients, evaluate,
    rationalSource, List.map_ofFn, List.sum_ofFn, Function.comp_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : r.index j = i
  · simp only [h, ite_true, hclear]
  · simp only [h, ite_false, Q.injective.eq_iff, Ne.symm h, mul_zero]

/-- The same bridge for the source's existing list representation. The
index equation is checked per input record, not assumed for the result. -/
theorem values_scaled_list {n : ℕ} (v : SparseField) (r : Records v.length n)
    (Q : Fin n ↪ Edge) (V : ℕ)
    (hindex : ∀ j, Q (r.index j) = (v.get j).1)
    (hclear : ∀ j, (((r.positive j : ℤ)-r.negative j : ℤ) : ℚ) = (V : ℚ)*(v.get j).2)
    (i : Fin n) : ((values r v.length).value i : ℚ) = (V : ℚ)*coefficients Q v i := by
  have hv : rationalSource (fun j => Q (r.index j)) (fun j => (v.get j).2) = v := by
    unfold rationalSource
    conv_rhs => rw [← List.ofFn_get v]
    congr 1
    funext j
    change (Q (r.index j), (v.get j).2) = v.get j
    rw [hindex]
  simpa only [hv] using values_scaled r Q (fun j => (v.get j).2) V hclear i

theorem cleared_channels (V : ℕ) (a : ℚ) (ha : a.den ∣ V) :
    ((((commonNumerator V a).toNat : ℤ)-(-commonNumerator V a).toNat : ℤ) : ℚ) =
      (V : ℚ)*a := by
  have hz : ((commonNumerator V a).toNat : ℤ)-(-commonNumerator V a).toNat =
      commonNumerator V a := by omega
  rw [hz, commonNumerator_scaled V a ha]

/-- Actual arrays initialized from individually cleared source entries have
the signed value required by `channelHorner_scaled`. Their channels are
allowed to retain cancelling positive and negative contributions. -/
theorem decoded_source_scaled {n : ℕ} (v : SparseField) (d : Data v.length n)
    (Q : Fin n ↪ Edge)
    (hindex : ∀ j, Q (d.records.index j) = (v.get j).1)
    (hp : ∀ j, d.records.positive j = (commonNumerator (sourceDenominator v) (v.get j).2).toNat)
    (hn : ∀ j, d.records.negative j = (-commonNumerator (sourceDenominator v) (v.get j).2).toNat)
    (i : Fin n) : ((values d.records v.length).value i : ℚ) =
      (sourceDenominator v : ℚ)*coefficients Q v i := by
  apply values_scaled_list v d.records Q (sourceDenominator v) hindex
  intro j
  rw [hp, hn]
  exact cleared_channels _ _ (has_sourceDenominator v (v.get j) (List.get_mem v j))

theorem decoded_source_integerValue {n : ℕ} (v : SparseField) (d : Data v.length n)
    (Q : Fin n ↪ Edge)
    (hindex : ∀ j, Q (d.records.index j) = (v.get j).1)
    (hp : ∀ j, d.records.positive j = (commonNumerator (sourceDenominator v) (v.get j).2).toNat)
    (hn : ∀ j, d.records.negative j = (-commonNumerator (sourceDenominator v) (v.get j).2).toNat)
    (i : Fin n) : (values d.records v.length).value i =
      (integerSource (coefficients Q v) (sourceDenominator v)).value i := by
  apply Int.cast_injective (α := ℚ)
  rw [decoded_source_scaled v d Q hindex hp hn]
  exact (integerSource_scaled (coefficients Q v) (sourceDenominator v)
    (fun k => (has_sourceDenominator v).evaluate (Q k)) i).symm

/-- Reading either initialized pair gives the same accumulated signed value. -/
theorem outputWords_signed_value {m n : ℕ} (d : Data m n)
    (hp : (∑ j, d.records.positive j).bits.length ≤ addressValue d.width)
    (hn : (∑ j, d.records.negative j).bits.length ≤ addressValue d.width) (i : Fin n)
    (pair : Fin 2) :
    (addressValue ((outputWords d m ⟨2*pair.val, by omega⟩).get i) : ℤ)-
      addressValue ((outputWords d m ⟨2*pair.val+1, by omega⟩).get i) =
      (values d.records m).value i := by
  have hpfit := values_positive_bits_le d.records m _ hp i
  have hnfit := values_negative_bits_le d.records m _ hn i
  rw [outputWords_value d m i _ hpfit hnfit, outputWords_value d m i _ hpfit hnfit]
  fin_cases pair <;> rfl

end Maxwell.Cost.CalibrationMatrix.SourceInit
