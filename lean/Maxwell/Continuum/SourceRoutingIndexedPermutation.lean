import Maxwell.Continuum.SourceRoutingIndexedPorts

namespace Maxwell.Logical.Routing.DummyFill
theorem extension_cast {k l n m : ℕ} (hk : k=l) (hn : n=m)
    (source target : Fin k→Fin n) (hs : Function.Injective source) (ht : Function.Injective target)
    (source' target' : Fin l→Fin m) (hs' : Function.Injective source') (ht' : Function.Injective target')
    (hsource : ∀i,source' (Fin.cast hk i)=Fin.cast hn (source i))
    (htarget : ∀i,target' (Fin.cast hk i)=Fin.cast hn (target i)) (i : Fin n) :
    extension source' target' hs' ht' (Fin.cast hn i)=Fin.cast hn (extension source target hs ht i) := by
  subst l
  subst m
  have he : source'=source := by funext j;simpa using hsource j
  have hf : target'=target := by funext j;simpa using htarget j
  subst source'
  subst target'
  rfl
end Maxwell.Logical.Routing.DummyFill

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePlan
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Logical.Routing.Gluing
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem indexed_size (S : Source.SparseSystem) (p : ℕ) :
    (2*portHalfSide (indexedVertices S p))*(2*portHalfSide (indexedVertices S p))=size S p := by
  rw [←half_indexed]
  exact size_eq S p

theorem indexedSource_injective (S : Source.SparseSystem) (p : ℕ) : Function.Injective (indexedSource S p) := by
  intro i j hij
  apply (finCongr (SourceGraph.Incidence.incidence_count S p)).injective
  apply source_injective S p
  apply Fin.ext
  exact (source_indexed S p i).trans ((congrArg Fin.val hij).trans (source_indexed S p j).symm)

theorem indexedTarget_injective (S : Source.SparseSystem) (p : ℕ) : Function.Injective (indexedTarget S p) := by
  intro i j hij
  apply (finCongr (SourceGraph.Incidence.incidence_count S p)).injective
  apply target_injective S p
  apply Fin.ext
  exact (target_indexed S p i).trans ((congrArg Fin.val hij).trans (target_indexed S p j).symm)

def indexedPermutation (S : Source.SparseSystem) (p : ℕ) :
    Equiv.Perm (Fin ((2*portHalfSide (indexedVertices S p))*(2*portHalfSide (indexedVertices S p)))) :=
  DummyFill.extension (indexedSource S p) (indexedTarget S p)
    (indexedSource_injective S p) (indexedTarget_injective S p)

theorem indexedPermutation_target (S : Source.SparseSystem) (p : ℕ) :
    (Composition.SourceRouting.indexedData S p).target=
      (finProdFinEquiv.trans (indexedPermutation S p)).trans finProdFinEquiv.symm := rfl

theorem permutation_indexed (S : Source.SparseSystem) (p : ℕ)
    (i : Fin ((2*portHalfSide (indexedVertices S p))*(2*portHalfSide (indexedVertices S p)))) :
    permutation S p (Fin.cast (indexed_size S p) i)=
      Fin.cast (indexed_size S p) (indexedPermutation S p i) :=
  DummyFill.extension_cast (SourceGraph.Incidence.incidence_count S p) (indexed_size S p)
    _ _ _ _ _ _ _ _ (fun j => Fin.ext (source_indexed S p j))
    (fun j => Fin.ext (target_indexed S p j)) i

def indexedPortIndex (S : Source.SparseSystem) (p : ℕ) :
    Port (2*portHalfSide (indexedVertices S p))≃Fin (size S p) :=
  finProdFinEquiv.trans (finCongr (indexed_size S p))

theorem permutation_port (S : Source.SparseSystem) (p : ℕ)
    (a : Port (2*portHalfSide (indexedVertices S p))) :
    permutation S p (indexedPortIndex S p a)=
      indexedPortIndex S p ((Composition.SourceRouting.indexedData S p).target a) := by
  rw [indexedPermutation_target]
  change permutation S p (Fin.cast (indexed_size S p) (finProdFinEquiv a))=
    Fin.cast (indexed_size S p) (finProdFinEquiv (finProdFinEquiv.symm (indexedPermutation S p (finProdFinEquiv a))))
  rw [Equiv.apply_symm_apply]
  exact permutation_indexed S p (finProdFinEquiv a)

#print axioms permutation_indexed
#print axioms permutation_port
end Maxwell.Cost.RoutingPorts.Complete.SourcePlan
