import Maxwell.Continuum.SourceRoutingSourcePhaseArrays

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePhase
open Maxwell.Logical Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem inverse_port (S : Source.SparseSystem) (p : ℕ)
    (a : Port (side S p)) :
    (SourcePlan.permutation S p).symm (SourcePlan.indexedPortIndex S p a)=
      SourcePlan.indexedPortIndex S p ((Composition.SourceRouting.indexedData S p).target.symm a) := by
  apply (SourcePlan.permutation S p).injective
  rw [Equiv.apply_symm_apply,SourcePlan.permutation_port,Equiv.apply_symm_apply]

theorem backward_values (S : Source.SparseSystem) (p : ℕ) (i : Fin (side S p*side S p)) :
    (GeometryPhase.targets (Composition.SourceRouting.indexedData S p).target.symm).get i=
      (((DummyFill.scatter ((DummyFill.pairs (SourcePlan.source S p) (SourcePlan.target S p)).map Prod.swap)).map Fin.val).get
        (Fin.cast (square S p) i)) := by
  simp only [GeometryPhase.targets,SortArrays.get_ofFn]
  rw [Tree.Storage.map_get]
  change (finProdFinEquiv ((Composition.SourceRouting.indexedData S p).target.symm (GeometryPhase.port i))).val=
    ((SourcePlan.permutation S p).symm (Fin.cast (square S p) i)).val
  have hp:=congrArg Fin.val (inverse_port S p (GeometryPhase.port i))
  have hi:=congrArg (SourcePlan.indexedPortIndex S p) (index_port S p i)
  simp only [Equiv.apply_symm_apply] at hi
  rw [←hi] at hp
  exact hp.symm

theorem backward_stored (S : Source.SparseSystem) (p : ℕ) (s : BitRAMState)
    (stored : Stored (Startup.gridLayout (SourcePlan.vertices S p) (SourceGraph.Positive.base S p))
      ((DummyFill.scatter (DummyFill.pairs (SourcePlan.source S p) (SourcePlan.target S p))).map Fin.val)
      ((DummyFill.scatter ((DummyFill.pairs (SourcePlan.source S p) (SourcePlan.target S p)).map Prod.swap)).map Fin.val) s) :
    BitArray.Represents s.memory (layout S p).backward (plan S p).width
      (IncidenceEncoding.words (plan S p).width
        (GeometryPhase.targets (Composition.SourceRouting.indexedData S p).target.symm)) := by
  have h:=stored.backward
  have hw : (SourcePlan.size S p).bits.length=(plan S p).width := by
    change _=(side S p*side S p).bits.length
    rw [square]
  change BitArray.Represents s.memory (layout S p).backward (SourcePlan.size S p).bits.length
    (IncidenceEncoding.words (SourcePlan.size S p).bits.length _) at h
  rw [hw] at h
  apply h.reindex _ (Fin.cast (square S p)) (fun _=>rfl)
  intro i
  rw [IncidenceEncoding.words_get,IncidenceEncoding.words_get,backward_values S p i]
  rfl

#print axioms backward_stored
end Maxwell.Cost.RoutingPorts.Complete.SourcePhase
