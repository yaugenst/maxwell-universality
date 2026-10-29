import Maxwell.Cost.CalibrationMatrix.Allocation.Code
import Maxwell.Cost.Structured.NatAssign.Bounds

namespace Maxwell.Cost.CalibrationMatrix.Allocation
open Structured

theorem costCap_le (n width capacity B : ℕ)
    (hn : n.bits.length ≤ B) (hw : width.bits.length ≤ B) (hc : capacity.bits.length ≤ B) :
    costCap n width capacity ≤ 3000*8^48*(B+2)^2 := by
  have valid : ∀ a ∈ plan, a.Valid ids := by
    simp [plan,setupPlan,densePlan,sparsePlan,NatAssign.Instruction.Valid,ids]
  have hb : ∀ i ∈ ids, (initial n width capacity i).bits.length ≤ B := by
    intro i _
    dsimp [initial]
    split_ifs <;> first | assumption | simp
  have hl : ∀ a ∈ plan, a.literalWidth ≤ B := by
    simp [plan,setupPlan,densePlan,sparsePlan,NatAssign.Instruction.literalWidth]
  have h := NatAssign.price_bound ids plan valid (initial n width capacity) B hb hl
  simpa only [costCap,show plan.length = 48 from rfl] using h

theorem dense_bits (n width i : ℕ) (hi : i < 16) :
    (denseBase n width i).bits.length ≤ 2*n.bits.length+width.bits.length+5 := by
  have hin : i.bits.length ≤ 4 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hi
  have hn2 := RationalAccumulator.bits_mul_le n n
  have hm := RationalAccumulator.bits_mul_le (n*n) width
  have htwice := RationalAccumulator.bits_mul_le 2 (n*n*width)
  have hs := RationalAccumulator.bits_mul_le n width
  have ho := RationalAccumulator.bits_mul_le i (n*width)
  have ha := RationalAccumulator.bits_add_le (2*(n*n*width)) (i*(n*width))
  simp only [show (2 : ℕ).bits.length = 2 from rfl] at htwice
  dsimp [denseBase,matrixSpan,vectorSpan]
  omega

theorem sparse_bits (n width capacity i : ℕ) (hi : i < 4) :
    (sparseBase n width capacity i).bits.length ≤
      2*n.bits.length+capacity.bits.length+width.bits.length+6 := by
  have hin : i.bits.length ≤ 2 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hi
  have hd := dense_bits n width 14 (by decide)
  have hs := RationalAccumulator.bits_mul_le capacity width
  have ho := RationalAccumulator.bits_mul_le i (capacity*width)
  have ha := RationalAccumulator.bits_add_le (denseBase n width 14) (i*(capacity*width))
  dsimp [sparseBase]
  omega

theorem memoryEnd_bits (n width capacity : ℕ) :
    (memoryEnd n width capacity).bits.length ≤
      2*n.bits.length+capacity.bits.length+width.bits.length+6 :=
  sparse_bits n width capacity 3 (by decide)

end Maxwell.Cost.CalibrationMatrix.Allocation
