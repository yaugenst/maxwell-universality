import Maxwell.Continuum.CalibrationSeedRootInitialize
import Maxwell.Continuum.CalibrationSeedRootTableMeaning

/-! One fixed machine measures and allocates storage, resets scratch,
constructs the actual counter, and produces every dense seed coefficient. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
attribute [local irreducible] initialCode tableCode Allocation.budget

def allocatedCode : Code := .seq initialCode tableCode
def allocatedCost (M D : ℕ) (n : ℕ→ℕ) (B H : ℕ) : ℕ :=
  initialCost n B H+tableCost M D (Allocation.budget n)
    (ArrayDecodeMachine.aliasRowCount (3*M+D)).bits.length

theorem allocated_executes (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (n : ℕ→ℕ) (v : ℕ→Parts) (B H : ℕ) (hB : 10≤B)
    (width : ∀k∈Allocation.allIds,(n k).bits.length≤B) (good : Good slots v)
    (entryValid : ∀i,(a.get i).Valid)
    (size : n 750=M) (degree : n 751=D) (dimension : n 785=aliasArraySize (3*M+D))
    (side : n 786=aliasSide (3*M+D)) (rows : n 787=ArrayDecodeMachine.aliasRowCount (3*M+D))
    (count : n 788=2*aliasArraySize (3*M+D))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank Allocation.allIds n s.val) (cache : a.Ready s) (raw : Ready slots v s)
    (four : RationalAccumulator.Blank s.val 4) (h37 : RationalAccumulator.Blank s.val 37)
    (h216 : RationalAccumulator.Blank s.val 216)
    (headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,Executes input tape allocatedCode cost s t ∧ cost≤allocatedCost M D n B H ∧
      Nonempty (TableState M D (Allocation.budget n) a v 0 t) ∧
      Good slots (resetParts v) ∧ t.val.inputHead=s.val.inputHead ∧
      t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output := by
  obtain ⟨c0,u,e0,h0,⟨state⟩,counter,vw,gw,cacheMeta,entries,f0⟩ := initial_executes M D a n v B H
    hB width good size degree dimension side rows count input tape s bank cache raw four h37 h216 headers
  rcases counter with ⟨origin,counter⟩
  have big : 2≤Allocation.budget n := (by decide : 2≤1000).trans (Allocation.budget_ge n)
  have length : (ArrayDecodeMachine.aliasRowCount (3*M+D)).bits.length≤Allocation.budget n := by
    rw [←rows]
    exact Allocation.budget_bound n 787 (by decide)
  obtain ⟨c1,t,_,e1,h1,ht,_,_,inp,rnd,out⟩ := table_executes M D (Allocation.budget n) a v big
    vw gw cacheMeta entries entryValid _ origin (addressValue_bits _) length input tape u state counter
  exact ⟨c0+c1,t,e0.seq e1,Nat.add_le_add h0 h1,ht,gw,
    inp.trans f0.inputHead,rnd.trans f0.randomCursor,out.trans f0.output⟩

theorem allocated_rootApply (M N : ℕ) [NeZero M] (scale : ℚ) (W ell : ℕ)
    (a : PartArray.Table (2*(2*rootDegree scale W ell+1)^3))
    (n : ℕ→ℕ) (v : ℕ→Parts) (B H : ℕ) (hB : 10≤B)
    (width : ∀k∈Allocation.allIds,(n k).bits.length≤B) (good : Good slots v)
    (entryValid : ∀i,(a.get i).Valid)
    (correct : CacheCorrect (rootDegree scale W ell) a
      (fun ν=>rectangleRational (computedRootCoefficient scale W ell ν)))
    (seed : ∀j,(v (28+j.val)).value=seedComponent N j)
    (size : n 750=M) (degree : n 751=rootDegree scale W ell)
    (dimension : n 785=aliasArraySize (3*M+rootDegree scale W ell))
    (side : n 786=aliasSide (3*M+rootDegree scale W ell))
    (rows : n 787=ArrayDecodeMachine.aliasRowCount (3*M+rootDegree scale W ell))
    (count : n 788=2*aliasArraySize (3*M+rootDegree scale W ell))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank Allocation.allIds n s.val) (cache : a.Ready s) (raw : Ready slots v s)
    (four : RationalAccumulator.Blank s.val 4) (h37 : RationalAccumulator.Blank s.val 37)
    (h216 : RationalAccumulator.Blank s.val 216)
    (headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t b,Executes input tape allocatedCode cost s t ∧
      cost≤allocatedCost M (rootDegree scale W ell) n B H ∧ b.OutputReady t ∧
      GlobalPower.tableData (3*M+rootDegree scale W ell) b=
        FourierData.rootApply scale W ell (Supercell.finiteSeed M N) ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output := by
  obtain ⟨cost,t,e,hc,⟨state⟩,gw,inp,rnd,out⟩ := allocated_executes M (rootDegree scale W ell)
    a n v B H hB width good entryValid size degree dimension side rows count input tape s
    bank cache raw four h37 h216 headers
  exact ⟨cost,t,state.table,e,hc,state.ready,state.rootApply correct entryValid gw seed,inp,rnd,out⟩

#print axioms allocated_rootApply
end Maxwell.Continuum.Calibration.SeedRoot
