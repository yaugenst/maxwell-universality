import Maxwell.Continuum.NearestIntegerExecution
import Maxwell.Continuum.RationalDataflowArrayOutputFrame

/-! Reusable frame rules for rounded rational arithmetic followed by an
indexed table write. They do not depend on a particular physical model. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000

theorem DyadicFloor.StoredPower.metadata_outside (S : Finset ℕ) (i : ℕ)
    (hi : (200 ≤ i ∧ i<220) ∨ (224 ≤ i ∧ i<1000)) : i∉DyadicFloor.StoredPower.workspace S := by
  have hr := outside_workspace S i (Or.inr ⟨by omega,by omega⟩)
  have hids : i∉ids S := fun h=>hr (Finset.mem_union_right _ h)
  simp (disch := omega) [DyadicFloor.StoredPower.workspace,DyadicFloor.workspace,
    DyadicFloor.allIds,DyadicFloor.extraIds,NaturalQuotient.workPorts,hids]
  omega

theorem PartArray.Table.OutputReady.rounded_frame {n : ℕ} {a : PartArray.Table n}
    {S : Finset ℕ} {v : ℕ→Parts} {s t : Store} (h : a.OutputReady s)
    (hr : RationalDataflow.Ready S v t) (f : BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace S) s.val t.val) :
    a.OutputReady t := by
  have outside (i : ℕ) (hi : i∈({5,6,7,8,9,37}:Finset ℕ)) :
      i∉DyadicFloor.StoredPower.workspace S := by
    have hbounds : (4 ≤ i ∧ i<30) ∨ (i=37) := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    have hids : i∉ids S := by
      intro hm
      rcases Finset.mem_union.mp hm with hp|hw
      · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
        have hpos := positivePort_ge j
        have hneg := negativePort_ge j
        have hden := denominatorPort_ge j
        simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hj
        omega
      · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton] at hw
        simp only [Finset.mem_insert,Finset.mem_singleton] at hi
        omega
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    simp (disch := omega) [DyadicFloor.StoredPower.workspace,DyadicFloor.workspace,
      DyadicFloor.allIds,DyadicFloor.extraIds,NaturalQuotient.workPorts,hids]
    omega
  have keep (i : ℕ) (hi : i∈({5,6,7,8,9,37}:Finset ℕ)) := f.tapes i (outside i hi)
  have scratch : BankArray.Scratch t.val :=
    ⟨hr.2 0 (by decide),hr.2 1 (by decide),hr.2 2 (by decide),hr.2 3 (by decide),
      blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1,
      blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1,
      blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1,
      blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩
  apply h.transfer f.memory _ scratch (blank_of_eq (keep 7 (by decide)) h.seven)
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
  · exact keep 37 (by decide)
  all_goals exact f.tapes _ (DyadicFloor.StoredPower.metadata_outside S _ (by decide))

theorem DyadicFloor.Clean.write_frame {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : BankArray.FrameExcept 37 s.val t.val) : DyadicFloor.Clean t.val := by
  refine ⟨blank_of_eq (f.2.2.2.1 4 (Or.inl rfl) (by decide)) h.1,?_⟩
  intro i hi
  have bounds : 10 ≤ i ∧ i ≠ 37 := by
    simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  exact blank_of_eq (f.2.2.2.1 i (Or.inr bounds.1) bounds.2) (h.2 i hi)

#print axioms PartArray.Table.OutputReady.rounded_frame
end Maxwell.Continuum.RationalDataflow
