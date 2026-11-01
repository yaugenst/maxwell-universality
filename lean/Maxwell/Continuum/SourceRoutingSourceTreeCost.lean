import Maxwell.Continuum.SourceRoutingSourceTree
import Maxwell.Continuum.SourceRoutingSourcePlanCost
import Maxwell.Continuum.SourceRoutingTreeStartupCost

namespace Maxwell.Cost.RoutingPorts.Complete.SourceTree
open SourceGraph.Positive
set_option maxHeartbeats 2800000
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024

def wordBound (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) : ℕ :=
  SourcePlan.wordBound S p room+
    Tree.runWidth (Tree.TreeStartup.heap (SourcePlan.depth S p) (SourcePlan.treeLayout S p).backward)
      (SourcePlan.depth S p) (SourcePlan.depth S p)

theorem cost_bound (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) :
    cost S p room≤2^702*(2^SourcePlan.depth S p+1)^3*(wordBound S p room+10)^4 := by
  let q:=2^SourcePlan.depth S p
  let W:=wordBound S p room+10
  have counts : 4*count S p≤SourcePlan.size S p:=by
    have inc:=SourcePlan.incidence_room S p
    have size:=SourcePlan.size_eq S p
    nlinarith only [inc,size]
  have square : SourcePlan.size S p=q^2:=by
    rw [←SourcePlan.tree_power,pow_add]
    dsimp only [q]
    ring
  have dimensions : SourcePlan.size S p+4*count S p+1≤2*(q+1)^3:=by
    rw [square] at counts ⊢
    have quadratic : q^2+4*count S p+1≤2*(q+1)^2:=by
      nlinarith only [counts,Nat.zero_le q]
    exact quadratic.trans (Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le q)) (by decide : (2:ℕ)≤3)))
  have a:=SourcePlan.cost_bound S p room
  have frontend : SourcePlan.cost S p room≤2^151*(q+1)^3*W^4:=by
    apply a.trans
    calc
      _≤2^150*(2*(q+1)^3)*W^3:=Nat.mul_le_mul (Nat.mul_le_mul_left _ dimensions)
        (Nat.pow_le_pow_left (by unfold W wordBound;omega) 3)
      _≤2^150*(2*(q+1)^3)*W^4:=Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by unfold W;omega) (by decide))
      _=2^151*(q+1)^3*W^4:=by ring
  have b:=Tree.CompleteTree.cost_polynomial (SourcePlan.depth S p)
    (SourcePlan.treeLayout S p).forward (SourcePlan.treeLayout S p).backward
    ((Nat.le_add_right _ _).trans (SourcePlan.forward_bound S p))
  have tree : Tree.CompleteTree.cost (SourcePlan.depth S p)
      (SourcePlan.treeLayout S p).forward (SourcePlan.treeLayout S p).backward≤2^700*(q+1)^3*W^4:=by
    apply b.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    unfold W wordBound
    omega
  unfold cost
  calc
    _≤2^151*(q+1)^3*W^4+2^700*(q+1)^3*W^4:=Nat.add_le_add frontend tree
    _=(2^151+2^700)*((q+1)^3*W^4):=by ring
    _≤2^702*((q+1)^3*W^4):=Nat.mul_le_mul_right _ (by norm_num)
    _=2^702*(q+1)^3*W^4:=by ring

#print axioms cost_bound
end Maxwell.Cost.RoutingPorts.Complete.SourceTree
