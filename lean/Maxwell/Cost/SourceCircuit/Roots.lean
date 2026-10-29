import Maxwell.Cost.SourceCircuit.Allocate

namespace Maxwell.Cost.SourceCircuit

def RepresentsRoots {n : ℕ} (bank : Logical.CopyBank n) (roots : Vector (List Bool) n) : Prop :=
  ∀ i, addressValue (roots.get i) = (bank.root i).val

/-- The root-table mutation proved for the finite program is precisely
the root update in the logical two-copy construction. -/
theorem representsRoots_split {n : ℕ} (bank : Logical.CopyBank n)
    (roots : Vector (List Bool) n) (i : Fin n) (next : List Bool)
    (hr : RepresentsRoots bank roots) (hn : addressValue next = bank.size) :
    RepresentsRoots (bank.splitRoot i) (roots.set i (Increment.bits next)) := by
  intro j
  have hset : (roots.set i (Increment.bits next)).get j =
      if i = j then Increment.bits next else roots.get j := by
    simp [Vector.get,Fin.cast,Array.getElem_set,Fin.ext_iff]
  by_cases hij : i = j
  · subst j
    rw [hset,ite_eq_left rfl,Increment.bits_value,hn]
    change bank.size + 1 =
      (if i = i then Fin.last (bank.size+1) else (bank.root i).castSucc.castSucc).val
    simp
  · rw [hset,ite_eq_right hij]
    change addressValue (roots.get j) =
      (if j = i then Fin.last (bank.size+1) else (bank.root j).castSucc.castSucc).val
    simpa [Ne.symm hij] using hr j

theorem split_leaf_value {n : ℕ} (bank : Logical.CopyBank n) (i : Fin n)
    (next : List Bool) (hn : addressValue next = bank.size) :
    addressValue next = (bank.splitLeaf i).val := hn

theorem split_next_value {n : ℕ} (bank : Logical.CopyBank n) (i : Fin n)
    (next : List Bool) (hn : addressValue next = bank.size) :
    addressValue (Increment.bits (Increment.bits next)) = (bank.splitRoot i).size := by
  rw [Increment.bits_value,Increment.bits_value,hn]
  rfl

end Maxwell.Cost.SourceCircuit
