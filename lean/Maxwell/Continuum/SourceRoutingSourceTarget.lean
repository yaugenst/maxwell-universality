import Maxwell.Continuum.SourceRoutingTreeComplete
import Maxwell.Continuum.SourceRoutingSourceWorkspace

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Storage
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem map_get {α β : Type*} {n : ℕ} (f : α→β) (v : Vector α n) (i : Fin n) :
    (v.map f).get i=f (v.get i) := by
  simp [Vector.get,Fin.cast]

theorem encoded {α : Type*} {n : ℕ} (idx : α≃Fin n) (values : Vector ℕ n)
    (memory : ℕ→Bool) (base : ℕ)
    (hs : BitArray.Represents memory base n.bits.length (encode values)) :
    IndexedMemory.Represents idx (fun p => values.get (idx p)) memory base n.bits.length := by
  intro p j hj
  simpa [encode,Vector.get,Fin.cast,IncidenceEncoding.word] using hs.bits (idx p) j hj

def pullback {n : ℕ} (rows columns : ℕ) (hsize : 2^(columns+rows)=n) (permutation : Equiv.Perm (Fin n)) :
    Targets.Target rows columns :=
  let idx:=(ColorData.index rows columns).trans (finCongr hsize)
  (idx.trans permutation).trans idx.symm

theorem pullback_value {n : ℕ} (rows columns : ℕ) (hsize : 2^(columns+rows)=n)
    (permutation : Equiv.Perm (Fin n)) (p : Maxwell.Logical.Routing.Coloring.Columns columns×Fin (2^rows)) :
    (ColorData.index rows columns (pullback rows columns hsize permutation p)).val=
      (permutation (((ColorData.index rows columns).trans (finCongr hsize)) p)).val := by
  let idx:=(ColorData.index rows columns).trans (finCongr hsize)
  have h : idx (pullback rows columns hsize permutation p)=permutation (idx p) := by
    simp only [pullback,idx,Equiv.trans_apply,Equiv.apply_symm_apply]
  exact congrArg Fin.val h

theorem pullback_symm {n : ℕ} (rows columns : ℕ) (hsize : 2^(columns+rows)=n)
    (permutation : Equiv.Perm (Fin n)) :
    (pullback rows columns hsize permutation).symm=pullback rows columns hsize permutation.symm := by
  apply Equiv.ext
  intro p
  rfl

theorem pullback_stored {n : ℕ} (rows columns : ℕ) (hsize : 2^(columns+rows)=n)
    (permutation : Equiv.Perm (Fin n)) (values : Vector ℕ n)
    (hvalues : ∀i,values.get i=(permutation i).val)
    (memory : ℕ→Bool) (base : ℕ)
    (hs : BitArray.Represents memory base n.bits.length (encode values)) :
    Permutation rows columns (pullback rows columns hsize permutation) memory base n.bits.length := by
  have stored:=encoded ((ColorData.index rows columns).trans (finCongr hsize)) values memory base hs
  have indexed:=(IndexedMemory.cast_index hsize (ColorData.index rows columns)
    (fun p => values.get (((ColorData.index rows columns).trans (finCongr hsize)) p)) memory base n.bits.length).mp stored
  apply (IndexedMemory.congr_value (ColorData.index rows columns) _ _ (fun p => ?_) memory base n.bits.length).mp indexed
  rw [hvalues,pullback_value]

#print axioms pullback_stored
end Maxwell.Cost.RoutingPorts.Complete.Tree.Storage

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePlan
open Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def depth (S : Source.SparseSystem) (p : ℕ) : ℕ := Nat.clog 4 (vertices S p)+1

theorem tree_count (S : Source.SparseSystem) (p : ℕ) : Tree.TreeStartup.count (depth S p)=size S p := by
  calc
    _ = (2^depth S p)^2 := by
      rw [Tree.TreeStartup.count,←pow_mul]
      congr 1
      omega
    _ = (2*2^Nat.clog 4 (vertices S p))^2 :=
      congrArg (fun x : ℕ => x^2) (pow_succ' 2 (Nat.clog 4 (vertices S p)))
    _ = _ := (Startup.gridSize_square (vertices S p)).symm

theorem tree_power (S : Source.SparseSystem) (p : ℕ) : 2^(depth S p+depth S p)=size S p :=
  tree_count S p

def permutation (S : Source.SparseSystem) (p : ℕ) : Equiv.Perm (Fin (size S p)) :=
  DummyFill.extension (source S p) (target S p) (source_injective S p) (target_injective S p)

def root (S : Source.SparseSystem) (p : ℕ) : Tree.Targets.Target (depth S p) (depth S p) :=
  Tree.Storage.pullback (depth S p) (depth S p) (tree_power S p) (permutation S p)

theorem forward_stored (S : Source.SparseSystem) (p : ℕ) (s : BitRAMState)
    (hs : Stored (Startup.gridLayout (vertices S p) (SourceGraph.Positive.base S p))
      ((DummyFill.scatter (DummyFill.pairs (source S p) (target S p))).map Fin.val)
      ((DummyFill.scatter ((DummyFill.pairs (source S p) (target S p)).map Prod.swap)).map Fin.val) s) :
    Tree.Storage.Permutation (depth S p) (depth S p) (root S p) s.memory
      (Startup.gridLayout (vertices S p) (SourceGraph.Positive.base S p)).forward
      (Tree.TreeStartup.wordWidth (depth S p)) := by
  have stored:=Tree.Storage.pullback_stored (depth S p) (depth S p) (tree_power S p) (permutation S p)
    _ (fun i => Tree.Storage.map_get Fin.val _ i) _ _ hs.forward
  have width : (size S p).bits.length=Tree.TreeStartup.wordWidth (depth S p) := by
    rw [←tree_count,Tree.CompleteTree.count_width]
  simpa only [root,width] using stored

theorem backward_stored (S : Source.SparseSystem) (p : ℕ) (s : BitRAMState)
    (hs : Stored (Startup.gridLayout (vertices S p) (SourceGraph.Positive.base S p))
      ((DummyFill.scatter (DummyFill.pairs (source S p) (target S p))).map Fin.val)
      ((DummyFill.scatter ((DummyFill.pairs (source S p) (target S p)).map Prod.swap)).map Fin.val) s) :
    Tree.Storage.Permutation (depth S p) (depth S p) (root S p).symm s.memory
      (Startup.gridLayout (vertices S p) (SourceGraph.Positive.base S p)).backward
      (Tree.TreeStartup.wordWidth (depth S p)) := by
  have stored:=Tree.Storage.pullback_stored (depth S p) (depth S p) (tree_power S p) (permutation S p).symm
    _ (fun i => Tree.Storage.map_get Fin.val _ i) _ _ hs.backward
  have width : (size S p).bits.length=Tree.TreeStartup.wordWidth (depth S p) := by
    rw [←tree_count,Tree.CompleteTree.count_width]
  change Tree.Storage.Permutation (depth S p) (depth S p)
    (Tree.Storage.pullback (depth S p) (depth S p) (tree_power S p) (permutation S p)).symm _ _ _
  rw [Tree.Storage.pullback_symm]
  simpa only [width] using stored

#print axioms forward_stored
#print axioms backward_stored
end Maxwell.Cost.RoutingPorts.Complete.SourcePlan
