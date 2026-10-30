import Maxwell.Continuum.SubdivisionIncidentCounts

/-! Original incidence counts are preserved by the actual chronological
subdivision; both endpoint positions are counted once per original edge. -/
noncomputable section
namespace Maxwell.Composition.SubdivisionSteps
open Maxwell.Logical.Routing
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000

private theorem fin_indicator (n k : ℕ) (hk : k<n) (p : Prop) :
    (∑t : Fin n,if t.val=k ∧ p then (1:ℕ) else 0)=if p then 1 else 0 := by
  have he (t : Fin n) : t.val=k ↔ t=⟨k,hk⟩ := ⟨fun h=>Fin.ext h,congrArg Fin.val⟩
  by_cases hp : p <;> simp [he,hp]

variable {V E : Type*} [Fintype E] {half : ℕ} (data : Gluing.Data V E half)

theorem incidentSteps_original_card (v : V) :
    (incidentSteps data (.inl v)).card=
      (Finset.univ.filter (fun p : E×Bool=>data.endpoint p.1 p.2=v)).card := by
  unfold incidentSteps
  rw [Finset.card_filter,Finset.card_filter,Fintype.sum_sigma,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  have hlen := length_ge_five data e
  have ht (t : Fin ((EdgeWalk.edgeWalk data e).length)) :
      (if (Sum.inl v:Subdivision.Vertex data)=left data ⟨e,t⟩ ∨
          (Sum.inl v:Subdivision.Vertex data)=right data ⟨e,t⟩ then (1:ℕ) else 0)=
        (if t.val=0 ∧ data.endpoint e false=v then 1 else 0)+
        (if t.val=(EdgeWalk.edgeWalk data e).length-1 ∧ data.endpoint e true=v then 1 else 0) := by
    have hleft : (Sum.inl v:Subdivision.Vertex data)=left data ⟨e,t⟩ ↔
        t.val=0 ∧ data.endpoint e false=v := eq_comm.trans (left_original data e t v)
    have hright : (Sum.inl v:Subdivision.Vertex data)=right data ⟨e,t⟩ ↔
        t.val=(EdgeWalk.edgeWalk data e).length-1 ∧ data.endpoint e true=v :=
      eq_comm.trans (right_original data e t v)
    rw [hleft,hright]
    split_ifs <;> first | omega | tauto
  calc
    _ = ∑t : Fin ((EdgeWalk.edgeWalk data e).length),
        ((if t.val=0 ∧ data.endpoint e false=v then (1:ℕ) else 0)+
        (if t.val=(EdgeWalk.edgeWalk data e).length-1 ∧ data.endpoint e true=v then 1 else 0)) :=
      Finset.sum_congr rfl (fun t _=>ht t)
    _ = _ := by
      rw [Finset.sum_add_distrib,fin_indicator _ 0 (by omega),
        fin_indicator _ ((EdgeWalk.edgeWalk data e).length-1) (by omega),Fintype.sum_bool]
      dsimp only
      exact Nat.add_comm _ _

#print axioms incidentSteps_original_card
end Maxwell.Composition.SubdivisionSteps
