import Maxwell.Continuum.SourceRoutingTraversalTargets
import Maxwell.Continuum.SourceRoutingTraversalMemory

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Traversal
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def Prefix (heap rows total : ℕ) (root : Targets.Target rows total) (upto : ℕ) (memory : ℕ→Bool) : Prop :=
  ∀d,d<upto→∀columns (h : total-d=columns+1),∀i : Fin (2^d),
    Outputs.At heap (2^(total+rows)) (total+rows+1) (levelNode d i) rows columns
      (Targets.level rows total d (columns+1) root h i) memory

theorem node_count_fits (rows total d columns : ℕ) (h : total-d=columns+1) :
    2*2^(columns+rows) ≤ 2^(total+rows) := by
  rw [←pow_succ']
  apply Nat.pow_le_pow_right (by decide)
  omega

theorem Prefix.preserve {heap rows total upto count : ℕ} {root : Targets.Target rows total}
    {before after : ℕ→Bool} (hs : Prefix heap rows total root upto before)
    (hf : Memory.Frame (block heap (2^(total+rows)) (total+rows+1) (2^upto-1))
      (count*stride (2^(total+rows)) (total+rows+1)) before after) :
    Prefix heap rows total root upto after := by
  intro d hd columns h i
  apply Outputs.At.preserve_before (first:=2^upto-1) (count:=count) ?_
    (node_count_fits rows total d columns h) (by omega) hf (hs d hd columns h i)
  have upper:= (level_range d i).2
  have power : (2 : ℕ)^(d+1) ≤ 2^upto := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem Prefix.append {heap rows total upto columns : ℕ} {root : Targets.Target rows total}
    {memory : ℕ→Bool} (hcol : total-upto=columns+1)
    (hs : Prefix heap rows total root upto memory)
    (level : ∀i : Fin (2^upto),Outputs.At heap (2^(total+rows)) (total+rows+1) (levelNode upto i)
      rows columns (Targets.level rows total upto (columns+1) root hcol i) memory) :
    Prefix heap rows total root (upto+1) memory := by
  intro d hd other ho i
  by_cases he : d=upto
  · subst d
    have hc : other=columns := by omega
    subst other
    exact level i
  · exact hs d (by omega) other ho i

theorem Prefix.root (heap rows columns : ℕ) (root : Targets.Target rows (columns+1)) (memory : ℕ→Bool)
    (hs : Outputs.At heap (2^(columns+1+rows)) (columns+1+rows+1) 0 rows columns root memory) :
    Prefix heap rows (columns+1) root 1 memory := by
  intro d hd other ho i
  have hd0 : d=0 := by omega
  subst d
  have hc : other=columns := by omega
  subst other
  have hi : i.val=0 := by have hh:=i.isLt;norm_num at hh;omega
  simpa only [levelNode,hi,pow_zero,Nat.sub_self,Nat.zero_add,Targets.level,
    Targets.family,Targets.castTarget] using hs

#print axioms Prefix.preserve
#print axioms Prefix.append
#print axioms Prefix.root
end Maxwell.Cost.RoutingPorts.Complete.Tree.Traversal
