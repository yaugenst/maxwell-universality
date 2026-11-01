import Maxwell.Cost.Array

/-! An array below a preserved memory boundary remains represented. -/
namespace Maxwell.Cost.BitArray

theorem Represents.prefix {n base width bound : ℕ} {before after : ℕ→Bool}
    {words : Vector (List Bool) n} (h : Represents before base width words)
    (same : ∀address,address<bound→after address=before address)
    (fits : base+n*width≤bound) : Represents after base width words := by
  refine ⟨h.length,?_⟩
  intro i j hj
  have endIndex := Nat.mul_le_mul_right width i.isLt
  have addressBound : base+i.val*width+j<bound := by
    simp only [Nat.succ_mul] at endIndex
    omega
  rw [same _ addressBound]
  exact h.bits i j hj

#print axioms Represents.prefix
end Maxwell.Cost.BitArray
