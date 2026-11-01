import Maxwell.Continuum.SourceRoutingGeometryStored

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open Maxwell.Logical.Routing Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration GeometryPath

def capacity (q v e : ℕ) : ℕ := 3*v+e*(1+3072*q)+1+3072*q

theorem flatMap_length_le {α β : Type*} (xs : List α) (f : α→List β) (bound : ℕ)
    (length : ∀x∈xs,(f x).length≤bound) : (xs.flatMap f).length≤xs.length*bound := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>
    have hx:=length x (by simp)
    have ht:=ih (fun y hy=>length y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem capacity_room {v e half : ℕ} (data : Gluing.Data (Fin v) (Fin e) half)
    (positive : 0<2*half) (saved : SourceEmission.Geometry v e)
    (paths : ∀i,saved.paths.get i=EdgeEmission.edge data (EdgeEmission.prepare data) i) :
    packedLength saved+1+3072*(2*half)≤capacity (2*half) v e := by
  have hp:=flatMap_length_le (List.finRange e) (fun i=>pathWords (saved.paths.get i)) (1+3072*(2*half))
    (fun i _=>by rw [pathWords_length,paths i];have h:=edge_words_bound data positive i;omega)
  rw [List.length_finRange] at hp
  rw [←packed_length]
  simp only [packed,List.length_append,triples_length,List.length_ofFn,capacity]
  omega

#print axioms capacity_room
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
