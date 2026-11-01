import Maxwell.Continuum.SourceRoutingGeometryEdgeCost

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
set_option maxHeartbeats 2800000
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024

theorem natural_width {q : ℕ} (p : Plan q) (n B value : ℕ) (bound : wordBound p n≤B)
    (size : value≤q*q) : value.bits.length≤B := by
  have bit:=Maxwell.Continuum.RationalWords.bits_mono size
  have history : p.path.history.width≤p.path.bound n:=by
    unfold GeometryPathPhase.Plan.bound GeometryHistory.Plan.bound
    omega
  exact bit.trans (history.trans (plan_bounds p n B bound).1)

theorem original_loop_cost {q : ℕ} (p : Plan q) (n B count : ℕ) (bound : wordBound p n≤B)
    (width : count.bits.length≤B) : originalLoopCost p n count≤2^150*(count+1)*(B+3)^2 := by
  let Q:=(B+3)^2
  have small : B≤Q:=by dsimp only [Q];nlinarith
  have one : 1≤Q:=by dsimp only [Q];nlinarith
  have counter : 13*count.bits.length+15≤28*Q:=by omega
  have clear : 6*count.bits.length+4≤10*Q:=by omega
  have main:=original_step_cost p n B bound
  change originalStepCost p n≤2^148*Q at main
  unfold originalLoopCost
  calc
    _≤(count+1)*(28*Q)+count*(2^148*Q)+10*Q:=by
      have a:=Nat.mul_le_mul_left (count+1) counter
      have b:=Nat.mul_le_mul_left count main
      omega
    _=(28*(count+1)+count*2^148+10)*Q:=by ring
    _≤2^150*(count+1)*Q:=Nat.mul_le_mul_right _ (by omega)

theorem edge_loop_cost {q : ℕ} (p : Plan q) (n B count : ℕ) (bound : wordBound p n≤B)
    (width : count.bits.length≤B) : edgeLoopCost p n count≤2^260*(count+1)*(q+1)*(B+3)^2 := by
  let Q:=(B+3)^2
  have small : B≤Q:=by dsimp only [Q];nlinarith
  have one : 1≤Q:=by dsimp only [Q];nlinarith
  have counter : 13*count.bits.length+15≤28*Q:=by omega
  have clear : 6*count.bits.length+4≤10*Q:=by omega
  have main:=edge_step_cost p n B bound
  change edgeStepCost p n≤2^258*(q+1)*Q at main
  unfold edgeLoopCost
  calc
    _≤(count+1)*(28*Q)+count*(2^258*(q+1)*Q)+10*Q:=by
      have a:=Nat.mul_le_mul_left (count+1) counter
      have b:=Nat.mul_le_mul_left count main
      omega
    _=(28*(count+1)+count*2^258*(q+1)+10)*Q:=by ring
    _≤2^260*(count+1)*(q+1)*Q:=Nat.mul_le_mul_right _ (by nlinarith)

theorem price_bound {q : ℕ} (p : Plan q) (n v e left B : ℕ)
    (bound : wordBound p n≤B) (vertices : v≤q*q) (edges : e≤q*q) (leftBound : left≤v) :
    price p n v e left≤2^263*(q+1)^3*(B+3)^2 := by
  let Q:=(B+3)^2
  have small : B≤Q:=by dsimp only [Q];nlinarith
  have one : 1≤Q:=by dsimp only [Q];nlinarith
  have vw:=natural_width p n B v bound vertices
  have ew:=natural_width p n B e bound edges
  have lw:=natural_width p n B left bound (leftBound.trans vertices)
  have rw:=natural_width p n B (v-left) bound ((Nat.sub_le _ _).trans vertices)
  have a:=original_loop_cost p n B left bound lw
  have b:=original_loop_cost p n B (v-left) bound rw
  have c:=edge_loop_cost p n B e bound ew
  change edgeLoopCost p n e≤2^260*(e+1)*(q+1)*Q at c
  have sum : left+(v-left)=v:=Nat.add_sub_of_le leftBound
  have counter : (15*left.bits.length+21)+300*(v.bits.length+left.bits.length+4)+
      (6*v.bits.length+11)+(15*e.bits.length+21)≤4096*Q:=by omega
  have original : originalLoopCost p n left+originalLoopCost p n (v-left)≤2^150*(v+2)*Q:=by
    have both:=Nat.add_le_add a b
    calc
      _≤2^150*(left+1)*Q+2^150*(v-left+1)*Q:=both
      _=2^150*(left+(v-left)+2)*Q:=by ring
      _=2^150*(v+2)*Q:=by rw [sum]
  have first : price p n v e left≤2^150*(v+2)*Q+2^260*(e+1)*(q+1)*Q+4096*Q:=by
    unfold price
    omega
  have both : price p n v e left≤2^262*(v+e+1)*(q+1)*Q:=by
    apply first.trans
    calc
      _=(2^150*(v+2)+2^260*(e+1)*(q+1)+4096)*Q:=by ring
      _≤2^262*(v+e+1)*(q+1)*Q:=Nat.mul_le_mul_right _ (by nlinarith)
  have size : v+e+1≤2*(q+1)^2:=by nlinarith
  calc
    price p n v e left≤2^262*(v+e+1)*(q+1)*Q:=both
    _≤2^262*(2*(q+1)^2)*(q+1)*Q:=by gcongr
    _=2^263*(q+1)^3*Q:=by ring

#print axioms price_bound
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
