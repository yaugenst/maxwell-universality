import Maxwell.Cost.CalibrationMatrix.SourceInit.Ready
import Maxwell.Cost.CalibrationMatrix.Horner.UniformWidth

namespace Maxwell.Cost.CalibrationMatrix.SourceInit
open scoped BigOperators

def totalBound {m n : ℕ} (d : Data m n) : ℕ :=
  max (∑ j, d.records.positive j) (∑ j, d.records.negative j)

theorem values_bounded {m n : ℕ} (d : Data m n) (k : ℕ) :
    (values d.records k).Bounded (totalBound d) :=
  fun i => ⟨(values_positive_le d.records k i).trans (Nat.le_max_left _ _),
    (values_negative_le d.records k i).trans (Nat.le_max_right _ _)⟩

/-- The single kernel width also covers the larger temporary channel sums
used while scattering duplicate source entries. -/
theorem totals_fit {m n : ℕ} (d : Data m n) (a D S N W : ℕ)
    (hw : Horner.uniformWidth n a (totalBound d) D S N ≤ W) :
    (∑ j, d.records.positive j).bits.length ≤ W ∧
      (∑ j, d.records.negative j).bits.length ≤ W := by
  have hpositive : 0 < (S+1)*(2*n*a+1)^2 := by positivity
  have hbound : totalBound d ≤ Horner.uniformPrefix n a (totalBound d) S := by
    simpa only [Horner.uniformPrefix,one_mul] using
      Nat.mul_le_mul_right (totalBound d) (show 1 ≤ (S+1)*(2*n*a+1)^2 by omega)
  have hsize : (totalBound d).size ≤ W := by
    have hmono := Nat.size_le_size hbound
    dsimp [Horner.uniformWidth] at hw
    omega
  constructor <;> rw [Nat.size_eq_bits_len]
  · exact (Nat.size_le_size (Nat.le_max_left _ _)).trans hsize
  · exact (Nat.size_le_size (Nat.le_max_right _ _)).trans hsize

end Maxwell.Cost.CalibrationMatrix.SourceInit
