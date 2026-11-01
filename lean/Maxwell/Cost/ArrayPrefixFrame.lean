import Maxwell.Cost.Array

/-! A represented finite array survives changes strictly after its end. -/
namespace Maxwell.Cost.BitArray

theorem Represents.memoryPrefix {n base width limit : ℕ} {memory other : ℕ→Bool}
    {words : Vector (List Bool) n} (h : Represents memory base width words)
    (end_le : base+n*width≤limit) (same : ∀k,k<limit → other k=memory k) :
    Represents other base width words := by
  refine ⟨h.length,?_⟩
  intro i j hj
  rw [same _ (by
    have bound:=Nat.mul_le_mul_right width (show i.val+1≤n by omega)
    nlinarith only [bound,hj,end_le])]
  exact h.bits i j hj

#print axioms Represents.memoryPrefix
end Maxwell.Cost.BitArray
