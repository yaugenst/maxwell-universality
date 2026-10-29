import Maxwell.Cost.SparseEmission.Encoding
import Maxwell.Logical.RationalValidity

namespace Maxwell.Cost.SparseEmission

/-- The two stored flag bits recover every actual source coefficient exactly. -/
theorem source_flag_value (S : Source.SparseSystem) (precision : ℕ)
    (e : Logical.RationalCode.Entry) (he : e ∈ Logical.sourceSquareEntries S precision) :
    flagValue (decide (e.value < 0)) (decide (e.value = 1/2 ∨ e.value = -1/2)) = e.value := by
  obtain ⟨w,hw⟩ := Logical.sourceSquareEntries_alphabet S precision e he
  rw [hw]
  cases w <;> norm_num [Logical.Weight.value,flagValue]

end Maxwell.Cost.SparseEmission
