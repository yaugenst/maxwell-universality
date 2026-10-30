import Maxwell.Continuum.RationalTaylorRuntime
import Maxwell.Continuum.RuntimeCounterClear
import Maxwell.Continuum.NatAssignCleanup

/-! A fixed Taylor call restores its runtime index and countdown words. -/
namespace Maxwell.Continuum.RationalTaylor.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def clearIndices : List NatAssign.Instruction := [.literal 607 0,.literal 608 0]
def cleanProgram (cycle : Cycle) (countTape : ℕ) : Code :=
  .seq (program cycle countTape) (.seq (.call (TapeOps.clear countTape)) (NatAssign.code clearIndices))
def cleanCost (N W L : ℕ) : ℕ := costBound N W L+6*L+6*(N+1).bits.length+33
def cleanValues (a b : ℕ) (cycle : Cycle) (N i : ℕ) : ℕ :=
  if i∈RationalTaylor.ids then RationalTaylor.values a b (cycleSigns cycle) N i else 0

theorem clean_executes (cycle : Cycle) (countTape N W : ℕ) (v : ℕ→ℕ)
    (hcount : countTape∉ids) (hc4 : 4≤countTape) (hW : 1≤W) (hw : ∀i∈ids,(v i).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (origin : ℤ) (s : Store)
    (hn : addressValue word=N) (hword : s.val.tapes countTape=BitTape.shifted word origin)
    (hs : NatAssign.Bank ids v s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (cleanProgram cycle countTape) cost s t ∧ cost≤cleanCost N W word.length ∧
      NatAssign.Bank ids (cleanValues (v 600) (v 601) cycle N) t.val ∧ NatAssign.Scratch t.val ∧
      Blank t.val countTape ∧ BinaryPrecision.Frame (loopWorkspace countTape) s.val t.val := by
  obtain ⟨c0,u,finalWord,e0,h0,hu,huw,hl,f0⟩ := program_executes cycle countTape N W v hcount hc4 hW hw
    input tape word origin s hn hword hs hz
  obtain ⟨r,e1,zr,f1⟩ := RuntimeCounter.clear_executes countTape input tape finalWord origin u huw
  have br : NatAssign.Bank ids (values (v 600) (v 601) (cycleSigns cycle) N) r.val := by
    intro i hi
    exact word_of_eq (f1.tapes i (by simp only [Finset.mem_singleton];intro he;subst i;exact hcount hi)) (hu.data.bank i hi)
  have zs : NatAssign.Scratch r.val := by
    intro i hi
    exact blank_of_eq (f1.tapes i (by simp only [Finset.mem_singleton];omega)) (hu.data.scratch i hi)
  have hvalid : ∀a∈clearIndices,a.Valid ids := by simp [clearIndices,NatAssign.Instruction.Valid,ids]
  obtain ⟨c2,t,e2,h2,bt,zt,f2⟩ := NatAssign.executes ids ids_ge clearIndices hvalid
    (values (v 600) (v 601) (cycleSigns cycle) N) input tape r br zs
  have hc2 : c2≤6*(N+1).bits.length+29 := by
    simpa [clearIndices,NatAssign.price,NatAssign.Instruction.price,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,values] using h2
  have hsub : NatAssign.changes clearIndices⊆loopWorkspace countTape := by
    intro i hi
    apply Finset.mem_insert_of_mem
    simp only [NatAssign.changes,clearIndices,List.map_cons,List.map_nil,List.toFinset_cons,
      List.toFinset_nil,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,
      NatAssign.Instruction.target] at hi
    simp only [workspace,RationalTaylor.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hcount' : countTape∉NatAssign.changes clearIndices := by
    intro hi
    simp [NatAssign.changes,clearIndices,NatAssign.Instruction.target] at hi
    have hc607 : countTape≠607 := by intro he;subst countTape;exact hcount (by simp [ids])
    have hc608 : countTape≠608 := by intro he;subst countTape;exact hcount (by simp [ids])
    omega
  refine ⟨c0+(6*finalWord.length+4+c2),t,e0.seq (e1.seq e2),?_,?_,zt,
    blank_of_eq (f2.tapes countTape hcount') zr,
    f0.trans ((f1.mono (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))).trans (f2.mono hsub))⟩
  · unfold cleanCost
    omega
  · intro i hi
    have hb := bt i hi
    simp only [ids,RationalTaylor.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl)
    all_goals simpa [clearIndices,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,cleanValues,RationalTaylor.ids] using hb

#print axioms clean_executes
end Maxwell.Continuum.RationalTaylor.Runtime
