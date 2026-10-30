import Maxwell.Continuum.SourceRoutingAssemblyWidths
import Maxwell.Continuum.SourceRoutingAssemblyMemory

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

structure Plan (rows columns depth : ℕ) where
  heap : ℕ
  rootCount : ℕ
  rootWidth : ℕ
  initial : ℕ→ℕ
  L : ℕ
  L_lower : 2 ≤ L
  count_fits : 2*2^(columns+rows) ≤ rootCount
  width_fits : columns+rows+2 ≤ rootWidth
  coordinates : AssemblyCoordinates.Stored initial heap rootCount rootWidth depth (columns+rows) 0
  zero : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,initial i=0
  words : ∀i∈Division.ids,(initial i).bits.length ≤ L
  nodes_width : (2^depth).bits.length ≤ L
  target : Fin (2^depth)→Targets.Target rows (columns+1)

def Plan.Inputs {rows columns depth : ℕ} (p : Plan rows columns depth) (processed : ℕ) (memory : ℕ→Bool) : Prop :=
  ∀i : Fin (2^depth),processed ≤ i.val→
    Outputs.At p.heap p.rootCount p.rootWidth (levelNode depth i) rows columns (p.target i) memory ∧
    ∀b,LabelsAt p.heap p.rootCount p.rootWidth (child (levelNode depth i) b) rows columns
      (ColorData.childTarget rows columns (p.target i) b) memory

def Plan.Done {rows columns depth : ℕ} (p : Plan rows columns depth) (processed : ℕ) (memory : ℕ→Bool) : Prop :=
  ∀i : Fin (2^depth),i.val<processed→
    LabelsAt p.heap p.rootCount p.rootWidth (levelNode depth i) rows (columns+1) (p.target i) memory

theorem Plan.inputs_preserved {rows columns depth : ℕ} (p : Plan rows columns depth)
    (i : Fin (2^depth)) (before after : ℕ→Bool)
    (hf : Memory.Frame (block p.heap p.rootCount p.rootWidth (levelNode depth i))
      (stride p.rootCount p.rootWidth) before after) (hi : p.Inputs i.val before) : p.Inputs (i.val+1) after := by
  intro j hj
  have data:=hi j (by omega)
  have different : levelNode depth j≠levelNode depth i := by dsimp only [levelNode];omega
  refine ⟨Outputs.preserve _ _ _ _ _ _ 0 0 different p.count_fits p.width_fits _ _ _ hf data.1,?_⟩
  intro b
  exact LabelsAt.preserve (child_ne_level depth j i b) (by have hh:=p.count_fits;omega)
    (by have hh:=p.width_fits;omega) hf (data.2 b)

theorem Plan.done_preserved {rows columns depth : ℕ} (p : Plan rows columns depth)
    (i : Fin (2^depth)) (before after : ℕ→Bool)
    (hf : Memory.Frame (block p.heap p.rootCount p.rootWidth (levelNode depth i))
      (stride p.rootCount p.rootWidth) before after) (hd : p.Done i.val before)
    (result : LabelsAt p.heap p.rootCount p.rootWidth (levelNode depth i) rows (columns+1) (p.target i) after) :
    p.Done (i.val+1) after := by
  intro j hj
  by_cases he : j=i
  · subst j;exact result
  · have different : levelNode depth j≠levelNode depth i := by
      intro h;apply he;apply Fin.ext;dsimp only [levelNode] at h;omega
    apply LabelsAt.preserve different ?_ ?_ hf (hd j (by
      have hne : j.val≠i.val := fun h => he (Fin.ext h)
      omega))
    · simpa only [show columns+1+rows=columns+rows+1 by omega,pow_succ'] using p.count_fits
    · have hw:=p.width_fits;omega

#print axioms Plan.inputs_preserved
#print axioms Plan.done_preserved
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
