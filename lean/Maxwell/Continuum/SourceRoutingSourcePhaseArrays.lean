import Maxwell.Continuum.SourceRoutingSourcePhasePlan

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePhase
open Maxwell.Logical Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem index_port (S : Source.SparseSystem) (p : ℕ) (i : Fin (side S p*side S p)) :
    (SourcePlan.indexedPortIndex S p).symm (Fin.cast (square S p) i)=GeometryPhase.port i := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

theorem target_values (S : Source.SparseSystem) (p : ℕ) (i : Fin (side S p*side S p)) :
    (GeometryPhase.targets (Composition.SourceRouting.indexedData S p).target).get i=
      (((DummyFill.scatter (DummyFill.pairs (SourcePlan.source S p) (SourcePlan.target S p))).map Fin.val).get
        (Fin.cast (square S p) i)) := by
  simp only [GeometryPhase.targets,SortArrays.get_ofFn]
  rw [Tree.Storage.map_get]
  change (finProdFinEquiv ((Composition.SourceRouting.indexedData S p).target (GeometryPhase.port i))).val=
    (SourcePlan.permutation S p (Fin.cast (square S p) i)).val
  have hp := congrArg Fin.val (SourcePlan.permutation_port S p (GeometryPhase.port i))
  have hi:=congrArg (SourcePlan.indexedPortIndex S p) (index_port S p i)
  simp only [Equiv.apply_symm_apply] at hi
  rw [←hi] at hp
  exact hp.symm

theorem label_values (S : Source.SparseSystem) (p : ℕ) (i : Fin (side S p*side S p)) :
    (GeometryPhase.labels (Composition.SourceRouting.indexedData S p).colors).get i=
      (SourcePlan.colorValues S p).get (Fin.cast (square S p) i) := by
  simp only [GeometryPhase.labels,SourcePlan.colorValues,SortArrays.get_ofFn]
  change side S p*((Composition.SourceRouting.indexedData S p).colors.color (GeometryPhase.port i)).val=
    2^SourcePlan.depth S p*((Composition.SourceRouting.indexedData S p).colors.color
      ((SourcePlan.indexedPortIndex S p).symm (Fin.cast (square S p) i))).val
  rw [index_port,←SourcePlan.indexed_side]

theorem target_stored (S : Source.SparseSystem) (p : ℕ) (s : BitRAMState)
    (stored : Stored (Startup.gridLayout (SourcePlan.vertices S p) (SourceGraph.Positive.base S p))
      ((DummyFill.scatter (DummyFill.pairs (SourcePlan.source S p) (SourcePlan.target S p))).map Fin.val)
      ((DummyFill.scatter ((DummyFill.pairs (SourcePlan.source S p) (SourcePlan.target S p)).map Prod.swap)).map Fin.val) s) :
    BitArray.Represents s.memory ((plan S p).base 0) (plan S p).width
      (IncidenceEncoding.words (plan S p).width
        (GeometryPhase.targets (Composition.SourceRouting.indexedData S p).target)) := by
  have h := stored.forward
  have hw : (SourcePlan.size S p).bits.length=(plan S p).width := by
    change _=(side S p*side S p).bits.length
    rw [square]
  change BitArray.Represents s.memory ((plan S p).base 0) (SourcePlan.size S p).bits.length
    (IncidenceEncoding.words (SourcePlan.size S p).bits.length _) at h
  rw [hw] at h
  apply h.reindex _ (Fin.cast (square S p)) (fun _ => rfl)
  intro i
  rw [IncidenceEncoding.words_get,IncidenceEncoding.words_get,target_values S p i]
  rfl

theorem labels_stored (S : Source.SparseSystem) (p : ℕ) (memory : ℕ→Bool)
    (labels : Tree.LabelsAt (Tree.TreeStartup.heap (SourcePlan.depth S p) (SourcePlan.treeLayout S p).backward)
      (Tree.TreeStartup.count (SourcePlan.depth S p)) (Tree.TreeStartup.wordWidth (SourcePlan.depth S p))
      0 (SourcePlan.depth S p) (SourcePlan.depth S p) (SourcePlan.root S p) memory) :
    BitArray.Represents memory ((plan S p).base 1) (plan S p).width
      (IncidenceEncoding.words (plan S p).width
        (GeometryPhase.labels (Composition.SourceRouting.indexedData S p).colors)) := by
  have h := SourcePlan.labels_colors S p memory labels
  have hw : (SourcePlan.size S p).bits.length=(plan S p).width := by
    change _=(side S p*side S p).bits.length
    rw [square]
  rw [←labels_base,hw] at h
  apply h.reindex _ (Fin.cast (square S p)) (fun _ => rfl)
  intro i
  rw [IncidenceEncoding.words_get,IncidenceEncoding.words_get,label_values S p i]

#print axioms target_stored
#print axioms labels_stored

end Maxwell.Cost.RoutingPorts.Complete.SourcePhase
