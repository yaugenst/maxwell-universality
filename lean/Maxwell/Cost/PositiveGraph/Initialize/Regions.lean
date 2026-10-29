import Maxwell.Cost.PositiveGraph.Initialize.Common

namespace Maxwell.Cost.PositiveGraph.Initialize

theorem Outside.preserves_before {base width n oldBase oldWidth oldN : ℕ}
    {s t : BitRAMState} {words : Vector (List Bool) oldN}
    (h : Outside base width n s t) (hsep : oldBase+oldN*oldWidth ≤ base)
    (ha : BitArray.Represents s.memory oldBase oldWidth words) :
    BitArray.Represents t.memory oldBase oldWidth words := by
  refine ⟨ha.1,?_⟩
  intro i j hj
  have hmul := Nat.mul_le_mul_right oldWidth (show i.val+1 ≤ oldN by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hmul
  rw [h _ (Or.inl (by omega))]
  exact ha.2 i j hj

theorem Outside.widen {base width n total : ℕ} {s t : BitRAMState}
    (h : Outside base width n s t) (hb : base+n*width ≤ total) : Outside 0 total 1 s t := by
  intro a ha
  apply h a (Or.inr ?_)
  simp only [Nat.one_mul,Nat.zero_add] at ha
  omega

end Maxwell.Cost.PositiveGraph.Initialize
