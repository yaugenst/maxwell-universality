import Maxwell.Continuum.SourceRoutingHistoriesGenerate

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistories
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def bound {q : ℕ} (p : GeometryPhase.Plan q) : ℕ :=
  p.bound+(historyPlan p 0).bound+(historyPlan p 1).bound+(historyPlan p 2).bound

theorem plan_bound {q : ℕ} (p : GeometryPhase.Plan q) (slot : Fin 3) : (historyPlan p slot).bound ≤ bound p := by
  have cases : slot=0 ∨ slot=1 ∨ slot=2 := by fin_cases slot <;> simp
  rcases cases with rfl|rfl|rfl <;> dsimp only [bound] <;> omega

theorem generateCost_polynomial {q : ℕ} (p : GeometryPhase.Plan q) (sequential : Sequential p) :
    generateCost p ≤ 2^214*(q+1)^3*(bound p+3)^2 := by
  let total := (q+1)^3*(bound p+3)^2
  have big : (bound p+3)^2 ≤ total := Nat.le_mul_of_pos_left _ (by positivity)
  have historyBound (slot : Fin 3) : GeometryHistory.generateCost (historyPlan p slot) ≤ 2^210*total := by
    have cost:=GeometryHistory.generateCost_polynomial (historyPlan p slot)
    have size:=Nat.pow_le_pow_left (Nat.add_le_add_right (plan_bound p slot) 3) 2
    calc
      _ ≤ 2^210*(q+1)^3*((historyPlan p slot).bound+3)^2 := cost
      _ ≤ 2^210*(q+1)^3*(bound p+3)^2 := Nat.mul_le_mul_left _ size
      _ = 2^210*total := by dsimp only [total];ring
  have restartBound (slot : Fin 3) : 2^40*((historyPlan p slot).bound+3)^2 ≤ 2^40*total :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.add_le_add_right (plan_bound p slot) 3) 2).trans big)
  have first : 2^50*(p.bound+3)^2 ≤ 2^50*total :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (show p.bound+3 ≤ bound p+3 by dsimp only [bound];omega) 2).trans big)
  have g0:=historyBound 0
  have g1:=historyBound 1
  have g2:=historyBound 2
  have r0:=restartBound 0
  have r1:=restartBound 1
  have result : generateCost p ≤ 2^214*total := by
    dsimp only [generateCost,GeometryHistory.appendCost]
    rw [sequential.1,sequential.2]
    omega
  simpa only [total,Nat.mul_assoc] using result

#print axioms generateCost_polynomial
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistories
