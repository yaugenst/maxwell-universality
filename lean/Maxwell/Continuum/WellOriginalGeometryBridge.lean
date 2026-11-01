import Maxwell.Continuum.WellOriginalPassInitialize
import Maxwell.Continuum.WellStrengthPassState
import Maxwell.Cost.ArrayFrame

/-! The original-source pass hands its checked strength prefix and shared
runtime bank to the geometry passes without reconstructing stored data. -/
namespace Maxwell.Continuum.RationalDataflow.WellOriginalPass
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem State.strengthState {n J index : ℕ} {p : Plan n J} {a : PartArray.Table J}
    {memory : ℕ→Bool} {s : Store} (h : State p a index memory s) :
    WellStrengthPass.State a p.precision p.values index s :=
  ⟨h.rational,h.clean,h.power,h.table,h.outputIndex⟩


theorem State.configuration {n J index : ℕ} {p : Plan n J} {a : PartArray.Table J}
    {memory : ℕ→Bool} {s : Store} (h : State p a index memory s) :
    WellStrengthPass.Configuration a p.precision p.budget p.metadataBudget p.prefixLimit := by
  refine ⟨h.metadata,h.fit,h.separated,?_⟩
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl
  · exact h.above.1
  · exact h.above.2.1
  · exact h.above.2.2

theorem State.geometry {n J N base width B index : ℕ} {p : Plan n J} {a : PartArray.Table J}
    {data : Vector ℕ N} {clock : List Bool} {constants gv : ℕ→ℕ} {s t : Store}
    (g : GeometryOutput.Context data base width B clock constants gv s)
    (h : State p a index s.val.memory t) (below : base+N*width ≤ p.prefixLimit)
    (keep : ∀k,preserved k→t.val.tapes k=s.val.tapes k) :
    GeometryOutput.Context data base width B clock constants gv t := by
  have ready : GeometryOutput.Ready gv t := by
    refine ⟨?_,h.table.scratch,h.table.seven⟩
    intro k hk
    exact word_of_eq (keep k (by
      simp only [GeometryOutput.ids,Finset.mem_erase,Finset.mem_Icc] at hk
      unfold preserved;omega)) (g.ready.bank k hk)
  exact ⟨ready,g.wordWidth,g.array.of_prefix below h.savedPrefix,
    BankArray.word_of_eq (keep 962 (by unfold preserved;omega)) g.clockWord,g.fixed⟩

#print axioms State.geometry
end Maxwell.Continuum.RationalDataflow.WellOriginalPass
