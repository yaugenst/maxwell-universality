import Maxwell.Continuum.SourceRoutingGeometryPhaseCost

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open GeometryPath GeometryPathPhase
set_option maxHeartbeats 2800000
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024

def secondPlan {q : ℕ} (p : Plan q) : GeometryPathPhase.Plan q:=p.path.following p.secondBefore
def thirdPlan {q : ℕ} (p : Plan q) : GeometryPathPhase.Plan q:=(secondPlan p).following p.thirdBefore
def wordBound {q : ℕ} (p : Plan q) (n : ℕ) : ℕ :=
  p.path.bound n+(secondPlan p).bound n+(thirdPlan p).bound n+p.backward.bits.length

theorem plan_bounds {q : ℕ} (p : Plan q) (n B : ℕ) (bound : wordBound p n≤B) :
    p.path.bound n≤B ∧ (secondPlan p).bound n≤B ∧ (thirdPlan p).bound n≤B := by
  unfold wordBound at bound
  omega

theorem edge_cost {q : ℕ} (p : Plan q) (n B : ℕ) (bound : wordBound p n≤B) :
    edgeCost p.path p.secondBefore p.thirdBefore n≤2^257*(q+1)*(B+3)^2 := by
  obtain ⟨b₀,b₁,b₂⟩:=plan_bounds p n B bound
  have f₀:=forward_phase_cost p.path n B b₀
  have f₁:=forward_append_cost p.path p.secondBefore n B b₀ b₁
  have f₂:=forward_append_cost (secondPlan p) p.thirdBefore n B b₁ b₂
  have r₀:=reverse_phase_cost (thirdPlan p) n B b₂
  have r₁:=reverse_append_cost (secondPlan p) p.thirdBefore n B b₁ b₂
  have r₂:=reverse_append_cost p.path p.secondBefore n B b₀ b₁
  dsimp only [secondPlan] at f₂ r₁
  dsimp only [thirdPlan,secondPlan] at r₀
  have f : networkForwardCost p.path p.secondBefore p.thirdBefore n≤2^254*(q+1)*(B+3)^2:=by
    unfold networkForwardCost
    simp only [Nat.mul_assoc] at f₀ f₁ f₂ ⊢
    omega
  have r : networkReverseCost p.path p.secondBefore p.thirdBefore n≤2^255*(q+1)*(B+3)^2:=by
    unfold networkReverseCost
    simp only [Nat.mul_assoc] at r₀ r₁ r₂ ⊢
    omega
  have t₀:=(terminal_width p.path n 0 (Nat.zero_le _)).trans b₀
  have t₂:=(terminal_width (thirdPlan p) n (2*q) le_rfl).trans b₂
  dsimp only [thirdPlan,secondPlan,GeometryPathPhase.Plan.following] at t₂
  have h₂ : p.path.history.following.following.bound≤B:=by
    change p.path.history.following.following.bound+(6*q+1).bits.length+2*n.bits.length+
      p.path.width+p.path.base.bits.length+64≤B at b₂
    omega
  have lastRound:=(p.path.history.following.following.layer_bound (2*q) le_rfl).trans h₂
  have a : (terminalBound (p.path.history.layer 0) 1 p.path.width p.path.base n+3)^2≤(B+3)^2:=by gcongr
  have b : (terminalBound (p.path.history.following.following.layer (2*q)) (2*q+1)
      p.path.width p.path.base n+3)^2≤(B+3)^2:=by gcongr
  have c : ((p.path.history.following.following.layer (2*q)).bound (2*q+1)+2)^2≤(B+3)^2:=by gcongr;omega
  unfold edgeCost terminalCost
  calc
    _≤2*(2^142*(B+3)^2)+2^254*(q+1)*(B+3)^2+2*(2^142*(B+3)^2)+
        2^16*(B+3)^2+2^255*(q+1)*(B+3)^2:=by gcongr
    _=(4*2^142+2^254*(q+1)+2^16+2^255*(q+1))*(B+3)^2:=by ring
    _≤2^257*(q+1)*(B+3)^2:=Nat.mul_le_mul_right _ (by omega)

theorem selection_width {q : ℕ} (p : Plan q) (n B : ℕ) (bound : wordBound p n≤B) :
    edgeSelectBound (p.path.history.layer 0) 1 p.backward≤B := by
  have h:=p.path.history.layer_bound 0 (Nat.zero_le _)
  simp only [Nat.zero_add] at h
  simp only [edgeSelectBound,wordBound,GeometryPathPhase.Plan.bound] at bound ⊢
  omega

theorem edge_step_cost {q : ℕ} (p : Plan q) (n B : ℕ) (bound : wordBound p n≤B) :
    edgeStepCost p n≤2^258*(q+1)*(B+3)^2 := by
  have main:=edge_cost p n B bound
  have select:=selection_width p n B bound
  have terminal:=(terminal_width p.path n 0 (Nat.zero_le _)).trans (plan_bounds p n B bound).1
  have a : (edgeSelectBound (p.path.history.layer 0) 1 p.backward+3)^2≤(B+3)^2:=by gcongr
  have b : (terminalBound (p.path.history.layer 0) 1 p.path.width p.path.base n+3)^2≤(B+3)^2:=by gcongr
  unfold edgeStepCost
  calc
    _≤2^257*(q+1)*(B+3)^2+2^130*(B+3)^2+2^120*(B+3)^2:=by gcongr
    _=(2^257*(q+1)+2^130+2^120)*(B+3)^2:=by ring
    _≤2^258*(q+1)*(B+3)^2:=Nat.mul_le_mul_right _ (by omega)

theorem original_step_cost {q : ℕ} (p : Plan q) (n B : ℕ) (bound : wordBound p n≤B) :
    originalStepCost p n≤2^148*(B+3)^2 := by
  have terminal:=(terminal_width p.path n 0 (Nat.zero_le _)).trans (plan_bounds p n B bound).1
  unfold originalStepCost
  gcongr

#print axioms edge_step_cost
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
