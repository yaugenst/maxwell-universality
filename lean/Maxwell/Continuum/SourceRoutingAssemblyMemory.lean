import Maxwell.Continuum.SourceRoutingLeafLabels
import Maxwell.Continuum.SourceRoutingTreeChildren

namespace Maxwell.Cost.RoutingPorts.Complete.Tree
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def LabelsAt (heap rootCount rootWidth node rows columns : ℕ) (target : Targets.Target rows columns)
    (memory : ℕ→Bool) : Prop :=
  StoredLabels rows columns target memory
    (Leaves.labelBase heap rootCount rootWidth node (2^(columns+rows)) (columns+rows+1)) (columns+rows+1)

theorem labelsAt_succ (heap rootCount rootWidth node rows columns : ℕ) (target : Targets.Target rows (columns+1))
    (memory : ℕ→Bool) : LabelsAt heap rootCount rootWidth node rows (columns+1) target memory ↔
      StoredLabels rows (columns+1) target memory
        (Leaves.labelBase heap rootCount rootWidth node (2*2^(columns+rows)) (columns+rows+2))
        (columns+rows+2) := by
  have count : (2 : ℕ)^(columns+1+rows)=2*2^(columns+rows) := by
    rw [show columns+1+rows=columns+rows+1 by omega,pow_succ']
  have width : columns+1+rows+1=columns+rows+2 := by omega
  simp only [LabelsAt,count,width]

theorem LabelsAt.preserve {heap rootCount rootWidth a b rows columns : ℕ}
    {target : Targets.Target rows columns} {before after : ℕ→Bool}
    (hab : a≠b) (hn : 2^(columns+rows) ≤ rootCount) (hw : columns+rows+1 ≤ rootWidth)
    (hf : Memory.Frame (block heap rootCount rootWidth b) (stride rootCount rootWidth) before after)
    (hs : LabelsAt heap rootCount rootWidth a rows columns target before) :
    LabelsAt heap rootCount rootWidth a rows columns target after := by
  apply (labels_vector rows columns target after _ _).mpr
  apply hf.represents ?_ ((labels_vector rows columns target before _ _).mp hs)
  have fits:=slab_fits heap rootCount rootWidth a (2^(columns+rows)) (columns+rows+1) 10 hn hw (by omega)
  exact Memory.other_block heap rootCount rootWidth a b _ _ _ hab fits.1 fits.2

theorem child_ne_level (d : ℕ) (i j : Fin (2^d)) (b : Bool) : child (levelNode d i) b≠levelNode d j := by
  rw [←Targets.heap_child]
  have hchild:=(level_range (d+1) (Targets.child d i b)).1
  have hparent:=(level_range d j).2
  omega

#print axioms LabelsAt.preserve
end Maxwell.Cost.RoutingPorts.Complete.Tree
