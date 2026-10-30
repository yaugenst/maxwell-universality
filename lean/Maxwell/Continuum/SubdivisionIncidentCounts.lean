import Maxwell.Composition.SourceEdgeEnumeration
import Maxwell.Composition.PhysicalDiagonal

/-! Exact incidence counts for chronological subdivisions. Internal samples
have two incident path steps; original vertices retain their original
incidence counts. These identities justify the finite strength emitter. -/
noncomputable section
namespace Maxwell.Composition.SubdivisionSteps
open Maxwell.Logical.Routing
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)

 theorem left_original (e : E) (t : Fin ((EdgeWalk.edgeWalk data e).length)) (v : V) :
    left data ⟨e,t⟩=Sum.inl v ↔ t.val=0 ∧ data.endpoint e false=v := by
  by_cases ht : t.val=0
  · have he : t=⟨0,by have := length_ge_five data e;omega⟩ := Fin.ext ht
    rw [he,left_zero]
    simp only [true_and]
    exact ⟨Sum.inl.inj,congrArg Sum.inl⟩
  · rw [left_internal data e t (by omega)]
    simp [ht]

 theorem right_original (e : E) (t : Fin ((EdgeWalk.edgeWalk data e).length)) (v : V) :
    right data ⟨e,t⟩=Sum.inl v ↔ t.val=(EdgeWalk.edgeWalk data e).length-1 ∧ data.endpoint e true=v := by
  by_cases ht : t.val=(EdgeWalk.edgeWalk data e).length-1
  · have he : t=⟨(EdgeWalk.edgeWalk data e).length-1,by have := length_ge_five data e;omega⟩ := Fin.ext ht
    rw [he,right_last]
    simp only [true_and]
    exact ⟨Sum.inl.inj,congrArg Sum.inl⟩
  · rw [right_internal data e t (by have := t.isLt;omega)]
    simp [ht]

 theorem left_internal_iff (e : E) (t : Fin ((EdgeWalk.edgeWalk data e).length))
    (f : E) (i : Fin ((EdgeWalk.edgeWalk data f).length-1)) :
    left data ⟨e,t⟩=Sum.inr ⟨f,i⟩ ↔ e=f ∧ t.val=i.val+1 := by
  constructor
  · intro h
    have hef := vertexAt_internal_edge data e t.castSucc f i h
    subst f
    have he := Subdivision.edgeVertex_injective data e (h.trans (at_internal data e i).symm)
    exact ⟨rfl,congrArg Fin.val he⟩
  · rintro ⟨rfl,h⟩
    have ht : t.castSucc=⟨i.val+1,by have := i.isLt;omega⟩ := Fin.ext h
    change vertexAt data e t.castSucc=_
    rw [ht,at_internal]

 theorem right_internal_iff (e : E) (t : Fin ((EdgeWalk.edgeWalk data e).length))
    (f : E) (i : Fin ((EdgeWalk.edgeWalk data f).length-1)) :
    right data ⟨e,t⟩=Sum.inr ⟨f,i⟩ ↔ e=f ∧ t.val=i.val := by
  constructor
  · intro h
    have hef := vertexAt_internal_edge data e t.succ f i h
    subst f
    have he := Subdivision.edgeVertex_injective data e (h.trans (at_internal data e i).symm)
    have hh := congrArg Fin.val he
    simp only [Fin.val_succ] at hh
    exact ⟨rfl,by omega⟩
  · rintro ⟨rfl,h⟩
    have ht : t.succ=⟨i.val+1,by have := i.isLt;omega⟩ := by
      apply Fin.ext
      change t.val+1=i.val+1
      omega
    change vertexAt data e t.succ=_
    rw [ht,at_internal]

variable [Fintype E]

def incidentSteps (v : Subdivision.Vertex data) : Finset (Step data) :=
  Finset.univ.filter (fun s=>v=left data s ∨ v=right data s)

theorem incidentSteps_internal (e : E) (i : Fin ((EdgeWalk.edgeWalk data e).length-1)) :
    incidentSteps data (.inr ⟨e,i⟩)=
      {⟨e,⟨i.val,by have := i.isLt;omega⟩⟩,⟨e,⟨i.val+1,by have := i.isLt;omega⟩⟩} := by
  ext s
  rcases s with ⟨f,t⟩
  simp only [incidentSteps,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
  erw [eq_comm (a := (Sum.inr ⟨e,i⟩ : Subdivision.Vertex data)) (b := left data ⟨f,t⟩),
    eq_comm (a := (Sum.inr ⟨e,i⟩ : Subdivision.Vertex data)) (b := right data ⟨f,t⟩),
    left_internal_iff,right_internal_iff]
  constructor
  · rintro (⟨rfl,ht⟩|⟨rfl,ht⟩)
    · exact Or.inr (congrArg (fun t=>Sigma.mk f t) (Fin.ext ht))
    · exact Or.inl (congrArg (fun t=>Sigma.mk f t) (Fin.ext ht))
  · rintro (h|h)
    · cases h
      exact Or.inr ⟨rfl,rfl⟩
    · cases h
      exact Or.inl ⟨rfl,rfl⟩

theorem incidentSteps_internal_card (e : E) (i : Fin ((EdgeWalk.edgeWalk data e).length-1)) :
    (incidentSteps data (.inr ⟨e,i⟩)).card=2 := by
  rw [incidentSteps_internal,Finset.card_pair]
  intro h
  have hh : i.val=i.val+1 := by
    have he := Sigma.mk.inj_iff.mp h
    exact congrArg Fin.val (eq_of_heq he.2)
  omega

#print axioms incidentSteps_internal_card
end Maxwell.Composition.SubdivisionSteps
