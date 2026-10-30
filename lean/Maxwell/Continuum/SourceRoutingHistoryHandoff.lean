import Maxwell.Continuum.SourceRoutingHistoryGenerate
import Maxwell.Continuum.SourceRoutingPhaseGenerate
import Maxwell.Continuum.SourceRoutingGeometryLoad

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistories
open Structured Maxwell.Logical.Routing GeometryArithmetic
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def historyPlan {q : ℕ} (p : GeometryPhase.Plan q) (slot : Fin 3) : GeometryHistory.Plan q :=
  ⟨p.base ⟨slot.val+2,by omega⟩,p.clock,p.positive,p.clock_length⟩

def handoff : List NatAssign.Instruction :=
  [.copy 1216 1215,.literal 1201 0,.literal 1202 1,.literal 1220 2,.literal 1218 0,
    .copy 1200 1225,.multiply 1200 1225,.multiply 1217 1225,.add 1225 1216,.literal 1225 0]
def handoffCode : Code := .seq (loadCode 711 1217) (NatAssign.code handoff)

theorem handoff_values {q : ℕ} (p : GeometryPhase.Plan q) :
    NatAssign.values handoff (Function.update (GeometryPhase.seed p (q*q)) 1217 p.width)=
      GeometrySort.seed ((historyPlan p 0).layer 0) 1 0 := by
  funext j
  simp only [handoff,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target]
  by_cases h25 : j=1225
  · subst j;simp [GeometrySort.seed]
  by_cases h16 : j=1216
  · subst j;simp [GeometryPhase.seed,GeometrySort.seed,historyPlan,GeometryHistory.Plan.layer,
      GeometryHistory.Plan.slab,GeometryHistory.Plan.stride,GeometryHistory.Plan.width,GeometryPhase.Plan.width];ring
  by_cases h18 : j=1218
  · subst j;simp [GeometrySort.seed]
  by_cases h20 : j=1220
  · subst j;simp [GeometrySort.seed]
  by_cases h2 : j=1202
  · subst j;simp [GeometrySort.seed]
  by_cases h1 : j=1201
  · subst j;simp [GeometrySort.seed]
  by_cases h15 : j=1215
  · subst j;simp [GeometryPhase.seed,GeometrySort.seed,historyPlan,GeometryHistory.Plan.layer,GeometryHistory.Plan.slab]
  simp only [Function.update_of_ne h25,Function.update_of_ne h16,Function.update_of_ne h18,
    Function.update_of_ne h20,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h15]
  by_cases h17 : j=1217
  · subst j;simp [GeometrySort.seed,GeometrySort.Plan.width,GeometryPhase.Plan.width]
  simp only [Function.update_of_ne h17,GeometryPhase.seed,GeometrySort.seed,h1,h2,h15,h16,h17,h18,h20,ite_false]

theorem handoff_executes {q : ℕ} (p : GeometryPhase.Plan q) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (GeometryPhase.seed p (q*q)) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) (width : Word s.val 711 p.width) :
    ∃steps t,Executes input tape handoffCode steps s t ∧ steps ≤ 2^50*(p.bound+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (GeometrySort.seed ((historyPlan p 0).layer 0) 1 0) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ BinaryPrecision.Frame GeometryArithmetic.work s.val t.val := by
  obtain ⟨c0,a,e0,h0,ba,za,a1249,f0⟩:=load_executes 711 1217 (by decide) (by decide)
    (GeometryPhase.seed p (q*q)) p.width input tape s bank ready privateBlank width
  have seedWidth:=GeometryPhase.seed_width p (q*q) le_rfl
  have loadedWidth (j : ℕ) (hj : j∈GeometryArithmetic.ids) :
      ((Function.update (GeometryPhase.seed p (q*q)) 1217 p.width) j).bits.length ≤ p.bound := by
    by_cases same : j=1217
    · simpa only [same,Function.update_self] using (natural_bits_length_le p.width).trans p.width_bound
    · simpa only [Function.update_of_ne same] using seedWidth j hj
  obtain ⟨c1,t,e1,h1,bt,zt,f1⟩:=stage handoff
    (by simp [handoff,NatAssign.Instruction.Valid,GeometryArithmetic.ids,GeometryArithmetic.controls])
    (Function.update (GeometryPhase.seed p (q*q)) 1217 p.width) p.bound loadedWidth
    (by simp only [handoff,List.mem_cons,List.not_mem_nil,or_false];intro a ha
        rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [NatAssign.Instruction.literalWidth,GeometryPhase.Plan.bound]
        rw [show (2 : ℕ).bits.length=2 by decide]
        omega) input tape a ba za
  refine ⟨c0+c1,t,e0.seq e1,?_,by simpa only [handoff_values] using bt,zt,
    RationalAccumulator.blank_of_eq (f1.tapes 1249 (by decide)) a1249,
    (f0.mono (by decide)).trans (f1.mono ?_)⟩
  · have oldWidth:=seedWidth 1217 (by decide)
    have newWidth:=(natural_bits_length_le p.width).trans p.width_bound
    change c1 ≤ 3000*8^10*(p.bound+2)^2 at h1
    nlinarith
  · intro j hj
    simp only [GeometryArithmetic.work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    tauto

#print axioms handoff_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistories
