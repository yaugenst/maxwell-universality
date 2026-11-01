import Maxwell.Continuum.SourceRoutingSourcePlanCost

/-! The permutation frontend uses logarithmic addresses. Its word envelope
depends linearly on the source graph's measured word widths. -/
namespace Maxwell.Cost.RoutingPorts.Complete.SourcePlan
open SourceGraph.Positive RationalAccumulator Maxwell.Logical.Routing
set_option maxHeartbeats 150000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency true

private theorem bits_le_self (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact Nat.lt_two_pow_self

private theorem bits_sum (a b : ℕ) : (a+b).bits.length≤a.bits.length+b.bits.length+1 :=
  (bits_add_le a b).trans (by omega)

private theorem clog_four_le_bits (n : ℕ) : Nat.clog 4 n ≤ n.bits.length := by
  apply Nat.clog_le_of_le_pow
  have h : n≤2^n.bits.length:=by simpa only [Nat.size_eq_bits_len] using (Nat.lt_size_self n).le
  exact h.trans
    (Nat.pow_le_pow_left (by decide : (2:ℕ)≤4) _)

def inputWidth (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  (dimension S p).bits.length+(count S p).bits.length+width S p+10

theorem wordBound_input (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) :
    wordBound S p room ≤ 200*inputWidth S p := by
  let d:=dimension S p
  let e:=count S p
  let w:=width S p
  let v:=vertices S p
  let b:=base S p
  let k:=Nat.clog 4 v
  let n:=Startup.gridSize v
  let f:=b+4*v
  let r:=f+n*n.bits.length
  have h2 : (2:ℕ).bits.length=2:=by decide
  have h3 : (3:ℕ).bits.length=2:=by decide
  have h4 : (4:ℕ).bits.length=3:=by decide
  have dv:=bits_mul_le 2 d
  have vertices:=bits_sum (2*d) e
  change v.bits.length ≤ (2*d).bits.length+e.bits.length+1 at vertices
  have count4:=bits_mul_le 4 e
  have wp:=bits_sum w 3
  have wb:=bits_le_self w
  have endpoints:=bits_mul_le (4*e) (w+3)
  have vertex2:=bits_mul_le 2 v
  have ranks:=bits_mul_le 2 (4*e)
  have middle:=bits_sum (4*e*(w+3)) (2*v)
  have diagonal:=bits_sum (4*e*(w+3)+2*v) (2*(4*e))
  change b.bits.length ≤ (4*e*(w+3)+2*v).bits.length+(2*(4*e)).bits.length+1 at diagonal
  have depth:=clog_four_le_bits v
  change k≤v.bits.length at depth
  have depthBits:=bits_le_self k
  have halfBits : (half S p).bits.length=k+1:=by
    change (2^k).bits.length=k+1
    rw [Nat.size_eq_bits_len,Nat.size_pow]
  have power : (4^k).bits.length=2*k+1:=by
    rw [show (4:ℕ)=2^2 by decide,←pow_mul,Nat.size_eq_bits_len,Nat.size_pow]
  have grid:=bits_mul_le 4 (4^k)
  change n.bits.length ≤ (4:ℕ).bits.length+(4^k).bits.length at grid
  have scaled:=bits_mul_le 4 v
  have forward:=bits_sum b (4*v)
  change f.bits.length ≤ b.bits.length+(4*v).bits.length+1 at forward
  have nwidth:=bits_le_self n.bits.length
  have slab:=bits_mul_le n n.bits.length
  have backward:=bits_sum f (n*n.bits.length)
  change r.bits.length ≤ f.bits.length+(n*n.bits.length).bits.length+1 at backward
  have rankBase:=bits_sum (4*e*(w+3)) (2*v)
  simp only [h2] at dv vertex2 ranks
  simp only [h3] at wp
  simp only [h4] at count4 grid scaled
  simp only [wordBound,Startup.sourceWidth,scale,Scatter.boundWidth,plan,Startup.gridLayout,
    Startup.layout,GraphIncidence.layout,inputWidth]
  dsimp only [d,e,w,v,b,k,n,f,r,SourcePlan.vertices,SourceGraph.Positive.base,Startup.gridSize] at *
  simp only [show (0:ℕ).bits.length=0 by decide]
  omega

theorem inputWidth_source (S : Source.SparseSystem) (p : ℕ) (dimension_le : S.n≤S.nnz) :
    inputWidth S p ≤ 40*(S.nnz.bits.length+p+1) := by
  have d:=Maxwell.Logical.sourceCircuit_size S p dimension_le
  have e:=Maxwell.Logical.sourceSquareEntries_length_le S p
  have db:=Maxwell.Continuum.RationalWords.bits_mono d
  have eb:=Maxwell.Continuum.RationalWords.bits_mono e
  have dm:=bits_mul_le 6 S.nnz
  have dp:=bits_mul_le (6*S.nnz) (p+1)
  have pb:=bits_le_self (p+1)
  have ps:=bits_le_self p
  have ec:=bits_mul_le 3 (dimension S p)
  simp only [show (6:ℕ).bits.length=3 by decide] at dm
  simp only [show (3:ℕ).bits.length=2 by decide] at ec
  change (dimension S p).bits.length≤(6*S.nnz*(p+1)).bits.length at db
  change (count S p).bits.length≤(3*dimension S p).bits.length at eb
  unfold inputWidth width SourceCircuit.InitializeMetadata.width SourceCircuit.InitializeMetadata.exponent
  simp only [←Nat.size_eq_bits_len]
  omega

#print axioms wordBound_input
#print axioms inputWidth_source
end Maxwell.Cost.RoutingPorts.Complete.SourcePlan
