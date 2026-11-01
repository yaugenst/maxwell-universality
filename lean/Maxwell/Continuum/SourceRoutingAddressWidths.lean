import Maxwell.Continuum.SourceRoutingSourceGeometryCost

/-! Address widths of the routing arrays are linear in the widths of their
dimensions and starting addresses. These estimates do not assume a source
promise or a particular choice of the routing grid. -/
namespace Maxwell.Cost.RoutingPorts.Complete
open RationalAccumulator
set_option maxHeartbeats 1800000
set_option maxRecDepth 20000

private theorem bits_le_self (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact Nat.lt_two_pow_self

theorem GeometryHistory.Plan.address_bound {q : ℕ} (p : GeometryHistory.Plan q) :
    p.bound ≤ 16*q.bits.length+2*p.base.bits.length+50 := by
  have square:=bits_mul_le q q
  have width:=bits_le_self (q*q).bits.length
  have stride:=bits_mul_le (q*q) (q*q).bits.length
  have twice:=bits_mul_le 2 q
  have rounds:=bits_add_le (2*q) 1
  have offset:=bits_mul_le (2*q+1) (q*q*(q*q).bits.length)
  have address:=bits_add_le p.base ((2*q+1)*(q*q*(q*q).bits.length))
  simp only [show (2:ℕ).bits.length=2 by decide] at twice
  simp only [show (1:ℕ).bits.length=1 by decide] at rounds
  unfold GeometryHistory.Plan.bound GeometryHistory.Plan.slab GeometryHistory.Plan.stride
    GeometryHistory.Plan.width
  omega

theorem PhaseStartup.bases_width (q forward backward : ℕ) (slot : Fin 5) :
    (bases q forward backward slot).bits.length ≤
      forward.bits.length+backward.bits.length+15*q.bits.length+19 := by
  have square:=bits_mul_le q q
  have width:=bits_le_self (q*q).bits.length
  have slab:=bits_mul_le (q*q) (q*q).bits.length
  have labelsMul:=bits_mul_le 11 (q*q*(q*q).bits.length)
  have labels:=bits_add_le backward (11*(q*q*(q*q).bits.length))
  have first:=bits_add_le (backward+11*(q*q*(q*q).bits.length)) (q*q*(q*q).bits.length)
  have twice:=bits_mul_le 2 q
  have rounds:=bits_add_le (2*q) 1
  have step:=bits_mul_le (2*q+1) (q*q*(q*q).bits.length)
  have second:=bits_add_le (backward+11*(q*q*(q*q).bits.length)+q*q*(q*q).bits.length)
    ((2*q+1)*(q*q*(q*q).bits.length))
  have third:=bits_add_le
    (backward+11*(q*q*(q*q).bits.length)+q*q*(q*q).bits.length+
      (2*q+1)*(q*q*(q*q).bits.length)) ((2*q+1)*(q*q*(q*q).bits.length))
  simp only [show (11:ℕ).bits.length=4 by decide] at labelsMul
  simp only [show (2:ℕ).bits.length=2 by decide] at twice
  simp only [show (1:ℕ).bits.length=1 by decide] at rounds
  fin_cases slot <;> dsimp [bases]
  all_goals omega

theorem GeometryHistories.address_bound {q : ℕ} (p : GeometryPhase.Plan q) (B : ℕ)
    (base : ∀ i,(p.base i).bits.length ≤ B) :
    bound p ≤ 50*q.bits.length+11*B+166 := by
  have first:=(historyPlan p 0).address_bound
  have second:=(historyPlan p 1).address_bound
  have third:=(historyPlan p 2).address_bound
  have square:=bits_mul_le q q
  have h0:=base 0
  have h1:=base 1
  have h2:=base 2
  have h3:=base 3
  have h4:=base 4
  change (historyPlan p 0).bound ≤ 16*q.bits.length+2*(p.base 2).bits.length+50 at first
  change (historyPlan p 1).bound ≤ 16*q.bits.length+2*(p.base 3).bits.length+50 at second
  change (historyPlan p 2).bound ≤ 16*q.bits.length+2*(p.base 4).bits.length+50 at third
  unfold bound GeometryPhase.Plan.bound GeometryPhase.Plan.width
  omega

theorem GeometryProducer.addressWidth_bound {q : ℕ} (h : GeometryHistory.Plan q)
    (backward capacity : ℕ) :
    addressWidth h backward capacity ≤
      40*q.bits.length+2*h.base.bits.length+capacity.bits.length+backward.bits.length+100 := by
  have square:=bits_mul_le q q
  have width:=bits_le_self (q*q).bits.length
  have stride:=bits_mul_le (q*q) (q*q).bits.length
  have twice:=bits_mul_le 2 q
  have rounds:=bits_add_le (2*q) 1
  have step:=bits_mul_le (2*q+1) (q*q*(q*q).bits.length)
  have next:=bits_add_le h.base ((2*q+1)*(q*q*(q*q).bits.length))
  have last:=bits_add_le (h.base+(2*q+1)*(q*q*(q*q).bits.length))
    ((2*q+1)*(q*q*(q*q).bits.length))
  have bound:=h.following.following.address_bound
  simp only [show (2:ℕ).bits.length=2 by decide] at twice
  simp only [show (1:ℕ).bits.length=1 by decide] at rounds
  change h.following.following.bound ≤ 16*q.bits.length+
    2*(h.base+(2*q+1)*(q*q*(q*q).bits.length)+(2*q+1)*(q*q*(q*q).bits.length)).bits.length+50 at bound
  unfold addressWidth
  omega

#print axioms GeometryHistories.address_bound
#print axioms GeometryProducer.addressWidth_bound
end Maxwell.Cost.RoutingPorts.Complete
