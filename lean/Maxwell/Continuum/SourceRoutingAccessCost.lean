import Maxwell.Cost.RoutingPorts.Complete.Common

/-! Uniform bit-work estimates for the actual indexed routing-array accesses. -/

namespace Maxwell.Cost.RoutingPorts.Complete
set_option maxHeartbeats 800000

theorem natural_bits_length_le (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))

theorem access_cost_bound (width index base B : ℕ) (payload : List Bool)
    (hpayload : payload.length=width) (hB : 1≤B) (hw : width≤B)
    (hu : width.bits.length+index.bits.length+base.bits.length+5≤2*B) :
    BankArray.costCap width.bits index.bits base.bits payload+102*width+100≤5000*B^2 := by
  let u := width.bits.length+index.bits.length+base.bits.length
  have hu' : u+5≤2*B := hu
  have hsq := Nat.pow_le_pow_left hu' 2
  have hm := Nat.mul_le_mul hw
    (show 15*(u+1+width)+24≤15*(3*B+1)+24 by omega)
  have hr : 40*(u+2*width+3)+102*width+104≤262*B+224 := by omega
  unfold BankArray.costCap ArrayAccess.costCap
  simp only [addressValue_bits,hpayload]
  change 1000*(u+5)^2+width*(15*(u+1+width)+24)+4+
    40*(u+width+width+3)+102*width+100≤_
  nlinarith only [hsq,hm,hr,hB]

theorem layout_access_bound {n : ℕ} (l : Layout n) (i : Fin n) (base : ℕ)
    (hb : base.bits.length≤l.forward.bits.length+l.backward.bits.length)
    (payload : List Bool) (hp : payload.length=n.bits.length) :
    BankArray.costCap n.bits.length.bits i.val.bits base.bits payload+
      102*n.bits.length+100≤operationCap l/2 := by
  have hi : i.val.bits.length≤n.bits.length := by
    simp only [Nat.size_eq_bits_len]
    exact Nat.size_le_size i.isLt.le
  have hn := natural_bits_length_le n.bits.length
  have hh := access_cost_bound n.bits.length i.val base (scale l) payload hp
    (by unfold scale;omega) (by unfold scale;omega) (by unfold scale;omega)
  have he : operationCap l/2=5000*(scale l)^2 := by
    unfold operationCap
    omega
  exact hh.trans_eq he.symm

#print axioms access_cost_bound
#print axioms layout_access_bound

end Maxwell.Cost.RoutingPorts.Complete
