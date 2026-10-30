import Maxwell.Continuum.SourceRoutingHistoriesFrame

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistories
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def generateCode : Code := .seq handoffCode (.seq GeometryHistory.generateCode
  (.seq GeometryHistory.appendCode GeometryHistory.appendCode))
def generateCost {q : ℕ} (p : GeometryPhase.Plan q) : ℕ :=
  2^50*(p.bound+3)^2+GeometryHistory.generateCost (historyPlan p 0)+
    GeometryHistory.appendCost (historyPlan p 0)+GeometryHistory.appendCost (historyPlan p 1)

theorem generate_executes {q : ℕ} {target : Equiv.Perm (Port q)} (p : GeometryPhase.Plan q)
    (sequential : Sequential p) (colors : RowColoring target)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (GeometryPhase.seed p (q*q)) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : GeometryPhase.Metadata p s.val) (count : Word s.val 709 (q*q))
    (innerBlank : Blank s.val 1240) (outerBlank : Blank s.val 1241)
    (initialKeys : ∀slot : Fin 3,BitArray.Represents s.val.memory (historyPlan p slot).base p.width
      (IncidenceEncoding.words p.width (keys colors slot))) :
    ∃steps t,Executes input tape generateCode steps s t ∧ steps ≤ generateCost p ∧
      GeometryHistory.Runtime (historyPlan p 2) (keys colors 2) (2*q) t ∧ Blank t.val 1241 ∧
      Stored p colors t.val.memory ∧ ArchiveFrame GeometryHistory.loopWork s.val t.val ∧
      MemoryFrame p s.val.memory t.val.memory := by
  obtain ⟨c0,a,e0,h0,ba,za,a1249,f0⟩:=handoff_executes p input tape s bank ready privateBlank metadata.width
  have ma:=metadata.frame (ArchiveFrame.of_binary f0) (by decide)
  have start : GeometryHistory.Runtime (historyPlan p 0) (keys colors 0) 0 a := by
    refine ⟨Nat.zero_le _,ba,za,a1249,
      RationalAccumulator.blank_of_eq (f0.tapes 1240 (by decide)) innerBlank,
      RationalAccumulator.word_of_eq (f0.tapes 709 (by decide)) count,⟨ma.width,ma.clock⟩,?_⟩
    intro j hj
    have hz : j=0 := by omega
    subst j
    simpa only [f0.memory,GeometryHistory.Plan.slab,Nat.zero_mul,Nat.add_zero,SortArrays.run,
      GeometryHistory.Plan.width,GeometryPhase.Plan.width] using initialKeys 0
  obtain ⟨c1,b,e1,h1,rb,b1241,f1,m1⟩:=GeometryHistory.generate_executes (historyPlan p 0)
    (keys colors 0) (keys_fit p colors 0) input tape a start
    (RationalAccumulator.blank_of_eq (f0.tapes 1241 (by decide)) outerBlank)
  have secondInput : BitArray.Represents b.val.memory (historyPlan p 0).following.base p.width
      (IncidenceEncoding.words p.width (keys colors 1)) := by
    rw [sequential.1]
    apply m1.represents (future_separated (historyPlan p 0) _ (by rw [sequential.1]))
    rw [f0.memory];exact initialKeys 1
  have thirdOrder : (historyPlan p 0).following.base ≤ (historyPlan p 2).base := by
    rw [sequential.1,←sequential.2]
    exact following_base_le _
  have thirdAtB : BitArray.Represents b.val.memory (historyPlan p 2).base p.width
      (IncidenceEncoding.words p.width (keys colors 2)) :=
    m1.represents (future_separated (historyPlan p 0) _ thirdOrder) (by rw [f0.memory];exact initialKeys 2)
  obtain ⟨c2,c,e2,h2,rc,c1241,f2,m2⟩:=GeometryHistory.append_executes (historyPlan p 0)
    (keys colors 0) (keys colors 1) (keys_fit p colors 1) input tape b rb b1241 secondInput
  have firstAtC:=GeometryHistory.earlier_stored rb.stored m2
  rw [sequential.1] at rc m2
  have thirdInput : BitArray.Represents c.val.memory (historyPlan p 1).following.base p.width
      (IncidenceEncoding.words p.width (keys colors 2)) := by
    rw [sequential.2]
    exact m2.represents (future_separated (historyPlan p 1) _ (by rw [sequential.2])) thirdAtB
  obtain ⟨c3,t,e3,h3,rt,t1241,f3,m3⟩:=GeometryHistory.append_executes (historyPlan p 1)
    (keys colors 1) (keys colors 2) (keys_fit p colors 2) input tape c rc c1241 thirdInput
  have secondAtT:=GeometryHistory.earlier_stored rc.stored m3
  have firstAtT:=past_stored (show (historyPlan p 0).following.base ≤ (historyPlan p 1).following.base by
    rw [sequential.2];exact thirdOrder) firstAtC m3
  rw [sequential.2] at rt m3
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,rt,t1241,?_,
    ((ArchiveFrame.of_binary f0).mono ?_).trans (f1.trans (f2.trans f3)),
    (MemoryFrame.of_eq p f0.memory).trans ((MemoryFrame.of_history p 0 m1).trans
      ((MemoryFrame.of_history p 1 m2).trans (MemoryFrame.of_history p 2 m3)))⟩
  · dsimp only [generateCost];omega
  · intro slot
    fin_cases slot
    · exact firstAtT
    · exact secondAtT
    · exact rt.stored
  · intro j hj
    exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ hj))

#print axioms generate_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistories
