import Maxwell.Continuum.SourceRoutingCompletion

/-! Exact chronological prefixes of the incidence scatter. Their final
arrays are the partial tables required by the sentinel completion machine. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Scatter
open Logical.Routing

def forward {k n : ℕ} (source target : Fin k→Fin n) (done : ℕ) : Vector ℕ n :=
  fill [] ((realPairs source target).take done)
def backward {k n : ℕ} (source target : Fin k→Fin n) (done : ℕ) : Vector ℕ n :=
  forward target source done

theorem forward_zero {k n : ℕ} (source target : Fin k→Fin n) :
    forward source target 0=Vector.replicate n n := rfl

theorem forward_step {k n : ℕ} (source target : Fin k→Fin n) (i : Fin k) :
    forward source target (i.val+1)=(forward source target i.val).set (source i) (target i).val := by
  unfold forward
  rw [List.take_succ_eq_append_getElem (by simp [realPairs]),fill_append]
  simp [realPairs]

theorem backward_step {k n : ℕ} (source target : Fin k→Fin n) (i : Fin k) :
    backward source target (i.val+1)=(backward source target i.val).set (target i) (source i).val :=
  forward_step target source i

theorem forward_complete {k n : ℕ} (source target : Fin k→Fin n)
    (hs : Function.Injective source) : forward source target k=table (realPairs source target) := by
  have hlen : (realPairs source target).length=k := by simp [realPairs]
  have hn : ((realPairs source target).map Prod.fst).Nodup := by
    simpa [realPairs,List.map_map,Function.comp_def] using (List.nodup_finRange k).map hs
  rw [forward,List.take_of_length_le hlen.le,fill_table,List.append_nil]
  exact table_perm (List.reverse_perm _) (by simpa only [List.map_reverse,List.nodup_reverse] using hn)

theorem backward_complete {k n : ℕ} (source target : Fin k→Fin n)
    (ht : Function.Injective target) :
    backward source target k=table ((realPairs source target).map Prod.swap) := by
  rw [backward,forward_complete target source ht]
  congr 1
  simp [realPairs,List.map_map,Function.comp_def]

#print axioms forward_complete

end Maxwell.Cost.RoutingPorts.Complete.Scatter
