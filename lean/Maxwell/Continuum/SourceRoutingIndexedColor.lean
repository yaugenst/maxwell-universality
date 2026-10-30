import Maxwell.Continuum.SourceRoutingIndexedPermutation

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.ColorData
open Maxwell.Logical.Routing Maxwell.Logical.Routing.Coloring
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def powerPorts (d q : ℕ) (hq : q=2^d) : Columns d×Fin (2^d)≃Port q :=
  ((columnsFinEquiv d).prodCongr (Equiv.refl _)).trans
    ((finCongr hq.symm).prodCongr (finCongr hq.symm))

theorem power_label (d q : ℕ) (hq : q=2^d) (target : Equiv.Perm (Port q))
    (p : Columns d×Fin (2^d)) :
    ((labels d d (((powerPorts d q hq).trans target).trans (powerPorts d q hq).symm)).get (index d d p)).val=
      q*((Gluing.powerColoring q d hq target).color (powerPorts d q hq p)).val := by
  subst q
  have ports : powerPorts d (2^d) rfl=(columnsFinEquiv d).prodCongr (Equiv.refl _) := by
    apply Equiv.ext
    intro a
    rfl
  rw [ports]
  rw [label_value]
  simp only [Gluing.powerColoring,rowColoring,transportProper,Equiv.symm_apply_apply]
end Maxwell.Cost.RoutingPorts.Complete.Tree.ColorData

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePlan
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Logical.Routing.Gluing
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem indexed_side (S : Source.SparseSystem) (p : ℕ) :
    2*portHalfSide (indexedVertices S p)=2^depth S p := by
  rw [←half_indexed]
  exact portSide_power_two (vertices S p)

def ports (S : Source.SparseSystem) (p : ℕ) :
    Coloring.Columns (depth S p)×Fin (2^depth S p)≃Port (2*portHalfSide (indexedVertices S p)) :=
  Tree.ColorData.powerPorts (depth S p) _ (indexed_side S p)

theorem ports_index (S : Source.SparseSystem) (p : ℕ) :
    (Tree.ColorData.index (depth S p) (depth S p)).trans (finCongr (tree_power S p))=
      (ports S p).trans (indexedPortIndex S p) := by
  apply Equiv.ext
  intro a
  apply Fin.ext
  change a.2.val+2^depth S p*(Coloring.columnsFinEquiv (depth S p) a.1).val=
    a.2.val+(2*portHalfSide (indexedVertices S p))*(Coloring.columnsFinEquiv (depth S p) a.1).val
  rw [indexed_side]

theorem root_indexed (S : Source.SparseSystem) (p : ℕ) :
    root S p=((ports S p).trans (Composition.SourceRouting.indexedData S p).target).trans (ports S p).symm := by
  apply Equiv.ext
  intro a
  apply ((ports S p).trans (indexedPortIndex S p)).injective
  rw [←ports_index]
  change ((Tree.ColorData.index (depth S p) (depth S p)).trans (finCongr (tree_power S p)))
    (Tree.Storage.pullback (depth S p) (depth S p) (tree_power S p) (permutation S p) a)=_
  simp only [Tree.Storage.pullback,Equiv.trans_apply,Equiv.apply_symm_apply]
  change permutation S p
    (((Tree.ColorData.index (depth S p) (depth S p)).trans (finCongr (tree_power S p))) a)=
    ((Tree.ColorData.index (depth S p) (depth S p)).trans (finCongr (tree_power S p)))
      ((ports S p).symm ((Composition.SourceRouting.indexedData S p).target (ports S p a)))
  rw [ports_index]
  change permutation S p (indexedPortIndex S p (ports S p a))=
    indexedPortIndex S p (ports S p ((ports S p).symm ((Composition.SourceRouting.indexedData S p).target (ports S p a))))
  rw [Equiv.apply_symm_apply]
  exact permutation_port S p (ports S p a)

theorem indexed_colors (S : Source.SparseSystem) (p : ℕ) :
    (Composition.SourceRouting.indexedData S p).colors=
      powerColoring _ (depth S p) (indexed_side S p) (Composition.SourceRouting.indexedData S p).target := by
  dsimp only [depth,vertices]
  simp only [←SourceGraph.Incidence.vertex_count]
  rfl

theorem root_label (S : Source.SparseSystem) (p : ℕ)
    (a : Coloring.Columns (depth S p)×Fin (2^depth S p)) :
    ((Tree.ColorData.labels (depth S p) (depth S p) (root S p)).get
      (Tree.ColorData.index (depth S p) (depth S p) a)).val=
      2^depth S p*((Composition.SourceRouting.indexedData S p).colors.color (ports S p a)).val := by
  rw [root_indexed]
  have h:=Tree.ColorData.power_label (depth S p) _ (indexed_side S p)
    (Composition.SourceRouting.indexedData S p).target a
  change _=2^depth S p*((Composition.SourceRouting.indexedData S p).colors.color _).val
  rw [indexed_colors]
  exact h.trans (congrArg (fun n : ℕ => n*
    ((powerColoring _ (depth S p) (indexed_side S p)
      (Composition.SourceRouting.indexedData S p).target).color (ports S p a)).val) (indexed_side S p))

#print axioms root_indexed
#print axioms root_label
end Maxwell.Cost.RoutingPorts.Complete.SourcePlan
