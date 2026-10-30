import Maxwell.Continuum.SourceRoutingTreeOutputs

/-! The stored split-color array is selected by runtime word-width
parity. No remembered pointer-doubling execution trace is required. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.ColorAddress
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def slot (width : ℕ) : ℕ := 2+2*((width+1)%2)

theorem after_parity (layout : DoublingPass.Layout) (rounds : ℕ) :
    DoublingPass.layoutAfter layout rounds=if rounds%2=0 then layout else layout.flip := by
  induction rounds with
  | zero => rfl
  | succ r ih =>
      rw [DoublingPass.layoutAfter,ih]
      have hm:=Nat.mod_lt r (by decide : 0<2)
      by_cases h : r%2=0
      · have hh : (r+1)%2=1 := by omega
        simp [h,hh]
      · have hh : (r+1)%2=0 := by omega
        simp [h,hh]

theorem bounds (width : ℕ) : 2 ≤ slot width ∧ slot width ≤ 4 := by
  have h:=Nat.mod_lt (width+1) (by decide : 0<2)
  dsimp only [slot];omega

theorem address (base forward backward k : ℕ) :
    ((RoutingAllocator.layout base (2*2^k) (k+2) forward backward).child (2*2^k)).colors=
      RoutingAllocator.slab base (2*2^k) (k+2) (slot (k+2)) := by
  change (DoublingPass.layoutAfter (RoutingAllocator.layout base (2*2^k) (k+2) forward backward).split.route
    (2*2^k).bits.length).newJump=_
  have width : (2*2^k).bits.length=k+2 := by rw [←pow_succ',Nat.size_eq_bits_len,Nat.size_pow]
  rw [width,after_parity]
  by_cases h : (k+2)%2=0
  · have hh : (k+2+1)%2=1 := by omega
    simp [h,slot,hh,RoutingAllocator.layout]
  · have hh : (k+2+1)%2=0 := by omega
    simp only [h,↓reduceIte,slot,hh,Nat.mul_zero,Nat.add_zero,RoutingAllocator.layout,DoublingPass.Layout.flip]

#print axioms address
end Maxwell.Cost.RoutingPorts.Complete.Tree.ColorAddress
