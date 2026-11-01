import Maxwell.Continuum.SourceRoutingSourceTreeLayout
import Maxwell.Cost.SelectedParameters.GeometricBounds

/-! Polynomial costs of the actual source permutation frontend, including
least-grid selection, allocation, incidence scatter, and dummy completion. -/
namespace Maxwell.Cost.RoutingPorts.Complete
set_option maxHeartbeats 2800000
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024

private theorem startup_cost (vertices diagonal B : ℕ)
    (width : Startup.sourceWidth vertices diagonal≤B)
    (exponent : Nat.clog 4 vertices≤B) (exponentBits : (Nat.clog 4 vertices).bits.length≤B) :
    Startup.cost vertices diagonal≤2^65*(B+10)^3 := by
  let Q:=(B+10)^3
  have small : B+10≤Q:=le_self_pow₀ (by omega) (by decide : (3:ℕ)≠0)
  have square : (B+10)^2≤Q:=Nat.pow_le_pow_right (by omega) (by decide)
  have vertexBits : vertices.bits.length≤B:=by unfold Startup.sourceWidth at width;omega
  have search:=SelectedParameters.Geometric.cost_combined (Nat.clog 4 vertices) 3 (vertices.bits.length+3)
  have searchBound : SelectedParameters.Geometric.initialCost (vertices.bits.length+3)+
      SelectedParameters.Geometric.searchCost (Nat.clog 4 vertices) 3 (vertices.bits.length+3)≤2^60*Q:=by
    apply search.trans
    calc
      _≤(3000*8^11+(3000*8^5+16002))*25*(2*(B+10))^3:=by gcongr <;> omega
      _=(8*(3000*8^11+(3000*8^5+16002))*25)*Q:=by dsimp only [Q];ring
      _≤2^60*Q:=Nat.mul_le_mul_right _ (by norm_num)
  have preparation : 3000*8^4*(vertices.bits.length+5)^2≤2^24*Q:=by
    calc
      _≤3000*8^4*(B+10)^2:=by gcongr;omega
      _≤3000*8^4*Q:=Nat.mul_le_mul_left _ square
      _≤2^24*Q:=Nat.mul_le_mul_right _ (by norm_num)
  have metadata : 2^60*(Startup.sourceWidth vertices diagonal+2)^2≤2^60*Q:=by
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) 2).trans square)
  have power : (Nat.clog 4 vertices+1)*(13*(Nat.clog 4 vertices).bits.length+25)≤38*Q:=by
    calc
      _≤(B+10)*(38*(B+10)):=Nat.mul_le_mul (by omega) (by omega)
      _=38*(B+10)^2:=by ring
      _≤38*Q:=Nat.mul_le_mul_left _ square
  unfold Startup.cost Size.rawPrice
  omega

private theorem initialization_cost {n : ℕ} (l : Layout n) (B : ℕ) (width : scale l≤B) :
    Initialize.cost l≤2^17*(n+1)*(B+10)^2 := by
  have bits : n.bits.length≤B:=by unfold scale at width;omega
  have main : 2*PositiveGraph.Initialize.fillCost n (scale l)≤44000*(n+1)*(B+10)^2:=by
    unfold PositiveGraph.Initialize.fillCost
    calc
      _=44000*(n+1)*(scale l+2)^2:=by ring
      _≤_:=by gcongr;omega
  have small : B+10≤(n+1)*(B+10)^2:=by
    have square : B+10≤(B+10)^2:=by nlinarith
    exact square.trans (Nat.le_mul_of_pos_left _ (by omega))
  unfold Initialize.cost
  simp only [Nat.mul_assoc] at main ⊢
  omega

private theorem permutation_cost {k n : ℕ} (p : Scatter.Plan k n) (B : ℕ)
    (routing : scale p.routing≤B) (width : Scatter.boundWidth p≤B) :
    Permutation.cost p≤2^144*(k+n+1)*(B+10)^2 := by
  let Q:=(B+10)^2
  have one : 1≤Q:=by dsimp only [Q];nlinarith
  have small : B≤Q:=by dsimp only [Q];nlinarith
  have bits : k.bits.length≤B:=by unfold Scatter.boundWidth at width;omega
  have operation : operationCap p.routing≤10000*Q:=by unfold operationCap Q;gcongr;omega
  have step : Scatter.stepCost p≤2^141*Q:=by
    have arithmetic : 2^140*(Scatter.boundWidth p+2)^2≤2^140*Q:=by unfold Q;gcongr;omega
    unfold Scatter.stepCost
    omega
  have main:=Nat.mul_le_mul_left k step
  have counter : (k+1)*(13*k.bits.length+15)≤28*(k+1)*Q:=by
    calc
      _≤(k+1)*(28*Q):=Nat.mul_le_mul_left _ (by omega)
      _=_:=by ring
  have scatter : Scatter.cost p≤2^142*(k+1)*Q:=by
    unfold Scatter.cost Scatter.loopCost
    have rest : 21*k.bits.length+23≤44*Q:=by omega
    calc
      _≤28*(k+1)*Q+k*(2^141*Q)+44*Q:=by omega
      _=(28*(k+1)+k*2^141+44)*Q:=by ring
      _≤2^142*(k+1)*Q:=Nat.mul_le_mul_right _ (by omega)
  have cursor : cursorCost p.routing≤2^17*(n+1)*Q:=by
    unfold cursorCost
    calc
      _≤(2*n+1)*(60004*Q):=Nat.mul_le_mul_left _ (by omega)
      _=(60004*(2*n+1))*Q:=by ring
      _≤2^17*(n+1)*Q:=Nat.mul_le_mul_right _ (by omega)
  unfold Permutation.cost
  calc
    _≤2^142*(k+1)*Q+2^17*(n+1)*Q:=Nat.add_le_add scatter cursor
    _=(2^142*(k+1)+2^17*(n+1))*Q:=by ring
    _≤2^144*(k+n+1)*Q:=Nat.mul_le_mul_right _ (by omega)

namespace SourcePlan
open SourceGraph.Positive

def wordBound (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) : ℕ :=
  Startup.sourceWidth (vertices S p) (base S p)+Nat.clog 4 (vertices S p)+
    (Nat.clog 4 (vertices S p)).bits.length+
    scale (Startup.gridLayout (vertices S p) (base S p))+Scatter.boundWidth (plan S p [] room)

theorem cost_bound (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) :
    cost S p room≤2^150*(size S p+4*count S p+1)*(wordBound S p room+10)^3 := by
  let B:=wordBound S p room
  have a:=startup_cost (vertices S p) (base S p) B (by unfold B wordBound;omega)
    (by unfold B wordBound;omega) (by unfold B wordBound;omega)
  have b:=initialization_cost (Startup.gridLayout (vertices S p) (base S p)) B (by unfold B wordBound;omega)
  have c:=permutation_cost (plan S p [] room) B (by change scale (Startup.gridLayout _ _)≤B;unfold B wordBound;omega)
    (by unfold B wordBound;omega)
  let Q:=(B+10)^3
  have square : (B+10)^2≤Q:=Nat.pow_le_pow_right (by omega) (by decide)
  have b' : Initialize.cost (Startup.gridLayout (vertices S p) (base S p))≤2^17*(size S p+1)*Q:=
    b.trans (Nat.mul_le_mul_left _ square)
  have c' : Permutation.cost (plan S p [] room)≤2^144*(4*count S p+size S p+1)*Q:=
    c.trans (Nat.mul_le_mul_left _ square)
  change Startup.cost (vertices S p) (base S p)≤2^65*Q at a
  unfold cost prepareCost
  calc
    _≤2^65*Q+2^17*(size S p+1)*Q+2^144*(4*count S p+size S p+1)*Q:=by omega
    _=(2^65+2^17*(size S p+1)+2^144*(4*count S p+size S p+1))*Q:=by ring
    _≤2^150*(size S p+4*count S p+1)*Q:=Nat.mul_le_mul_right _ (by omega)

#print axioms cost_bound
end SourcePlan
end Maxwell.Cost.RoutingPorts.Complete
