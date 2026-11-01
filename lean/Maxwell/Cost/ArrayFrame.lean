import Maxwell.Cost.Array

/-! A represented packed array survives any change outside its finite
memory interval. This frame rule is independent of the producing program. -/
namespace Maxwell.Cost.BitArray

theorem Represents.of_agree {n base width : ℕ} {words : Vector (List Bool) n}
    {memory current : ℕ→Bool} (h : Represents memory base width words)
    (keep : ∀k,base ≤ k→k<base+n*width→current k=memory k) : Represents current base width words := by
  refine ⟨h.length,?_⟩
  intro i j hj
  rw [keep _ (by omega) _]
  · exact h.bits i j hj
  · have hi := Nat.mul_le_mul_right width (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hi
    omega

theorem Represents.of_prefix {n base width boundary : ℕ} {words : Vector (List Bool) n}
    {memory current : ℕ→Bool} (h : Represents memory base width words)
    (below : base+n*width ≤ boundary) (keep : ∀k,k<boundary→current k=memory k) :
    Represents current base width words :=
  h.of_agree (fun k _ hk=>keep k (hk.trans_le below))

#print axioms Represents.of_prefix
end Maxwell.Cost.BitArray
