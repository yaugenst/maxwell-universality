import Maxwell.Continuum.SourceRoutingLevelHandoff

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Targets
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def level (rows total d columns : ℕ) (root : Target rows total) (h : total-d=columns) :
    Fin (2^d)→Target rows columns := fun i => castTarget rows h (family rows total root d i)

theorem castTarget_rfl (rows columns : ℕ) (target : Target rows columns) :
    castTarget rows rfl target=target := rfl

theorem castTarget_trans (rows a b c : ℕ) (h : a=b) (j : b=c) (target : Target rows a) :
    castTarget rows j (castTarget rows h target)=castTarget rows (h.trans j) target := by
  subst b;subst c;rfl

theorem level_child (rows total d columns : ℕ) (root : Target rows total)
    (h : total-d=columns+1) (i : Fin (2^d)) (b : Bool) :
    level rows total (d+1) columns root (by omega) (child d i b)=
      ColorData.childTarget rows columns (level rows total d (columns+1) root h i) b := by
  have hd : d<total := by omega
  have hcol : total-(d+1)=columns := by omega
  subst columns
  simp only [level,family_child rows total d root hd,castTarget_rfl,atParent]

theorem level_next (rows total d columns : ℕ) (root : Target rows total)
    (h : total-d=columns+1+1) :
    level rows total (d+1) (columns+1) root (by omega)=
      Level.nextTargets rows columns d (level rows total d (columns+1+1) root h) := by
  funext i
  have hh:=level_child rows total d (columns+1) root h (parent d i) (bit i)
  rw [child_parent] at hh
  exact hh

#print axioms level_child
#print axioms level_next
end Maxwell.Cost.RoutingPorts.Complete.Tree.Targets
