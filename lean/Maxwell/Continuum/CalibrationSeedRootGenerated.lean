import Maxwell.Continuum.CalibrationSeedRootAllocated
import Maxwell.Continuum.CalibrationSeedRootShape

/-! Fixed dense seed generation from the cached coefficients, computed seed
components, and two scalar shape inputs. All counts and widths are executed. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
attribute [local irreducible] allocatedCode Allocation.budget

def generatedCode : Code := .seq (NatAssign.code shapePlan) allocatedCode
def generatedCost (M D : ℕ) (n : ℕ→ℕ) (B H : ℕ) : ℕ :=
  shapeCost B+allocatedCost M D (shapeValues n) (shapeWidth B) H

theorem generated_executes (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (n : ℕ→ℕ) (v : ℕ→Parts) (B H : ℕ) (hB : 10≤B)
    (width : ∀k∈Allocation.allIds,(n k).bits.length≤B) (good : Good slots v)
    (entryValid : ∀i,(a.get i).Valid) (size : n 750=M) (degree : n 751=D)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank Allocation.allIds n s.val) (cache : a.Ready s) (raw : Ready slots v s)
    (four : RationalAccumulator.Blank s.val 4) (h37 : RationalAccumulator.Blank s.val 37)
    (h216 : RationalAccumulator.Blank s.val 216)
    (headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,Executes input tape generatedCode cost s t ∧ cost≤generatedCost M D n B H ∧
      Nonempty (TableState M D (Allocation.budget (shapeValues n)) a v 0 t) ∧
      Good slots (resetParts v) ∧ t.val.inputHead=s.val.inputHead ∧
      t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output := by
  obtain ⟨c0,u,e0,h0,nu,wu,ru,au,f0⟩ := shape_executes a Allocation.allIds Allocation.allIds_ge
    (by decide) n v B (by omega) width input tape s bank raw cache
  have big : 10≤shapeWidth B := by
    have h : 1≤2^shapePlan.length := Nat.one_le_pow _ _ (by decide)
    have hm:=Nat.mul_le_mul_right (B+1) h
    unfold shapeWidth
    omega
  have size0 : shapeValues n 750=M :=
    (NatAssign.values_preserves shapePlan n 750 (by decide)).trans size
  have degree0 : shapeValues n 751=D :=
    (NatAssign.values_preserves shapePlan n 751 (by decide)).trans degree
  have fields:=shapeValues_fields n
  rw [size,degree] at fields
  have headers0 : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H u.val := by
    intro k hk
    obtain ⟨xs,hl,word⟩:=headers k hk
    have outside:k∉workspace:=by
      simp only [PowerMachine.BufferNorm.Allocation.clearHeaders,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl <;> decide
    exact ⟨xs,hl,BankArray.word_of_eq (f0.tapes k outside) word⟩
  obtain ⟨c1,t,e1,h1,state,gw,inp,rnd,out⟩ := allocated_executes M D a (shapeValues n) v (shapeWidth B) H
    big wu good entryValid size0 degree0 fields.1 fields.2.1 fields.2.2.1 fields.2.2.2 input tape u
    nu au ru (RationalAccumulator.blank_of_eq (f0.tapes 4 (by decide)) four)
    (RationalAccumulator.blank_of_eq (f0.tapes 37 (by decide)) h37)
    (RationalAccumulator.blank_of_eq (f0.tapes 216 (by decide)) h216) headers0
  exact ⟨c0+c1,t,e0.seq e1,Nat.add_le_add h0 h1,state,gw,
    inp.trans f0.inputHead,rnd.trans f0.randomCursor,out.trans f0.output⟩

theorem generated_rootApply (M N : ℕ) [NeZero M] (scale : ℚ) (W ell : ℕ)
    (a : PartArray.Table (2*(2*rootDegree scale W ell+1)^3))
    (n : ℕ→ℕ) (v : ℕ→Parts) (B H : ℕ) (hB : 10≤B)
    (width : ∀k∈Allocation.allIds,(n k).bits.length≤B) (good : Good slots v)
    (entryValid : ∀i,(a.get i).Valid)
    (correct : CacheCorrect (rootDegree scale W ell) a
      (fun ν=>rectangleRational (computedRootCoefficient scale W ell ν)))
    (seed : ∀j,(v (28+j.val)).value=seedComponent N j)
    (size : n 750=M) (degree : n 751=rootDegree scale W ell)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank Allocation.allIds n s.val) (cache : a.Ready s) (raw : Ready slots v s)
    (four : RationalAccumulator.Blank s.val 4) (h37 : RationalAccumulator.Blank s.val 37)
    (h216 : RationalAccumulator.Blank s.val 216)
    (headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t b,Executes input tape generatedCode cost s t ∧
      cost≤generatedCost M (rootDegree scale W ell) n B H ∧ b.OutputReady t ∧
      GlobalPower.tableData (3*M+rootDegree scale W ell) b=
        FourierData.rootApply scale W ell (Supercell.finiteSeed M N) ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output := by
  obtain ⟨cost,t,e,hc,⟨state⟩,gw,inp,rnd,out⟩ := generated_executes M (rootDegree scale W ell)
    a n v B H hB width good entryValid size degree input tape s bank cache raw four h37 h216 headers
  exact ⟨cost,t,state.table,e,hc,state.ready,state.rootApply correct entryValid gw seed,inp,rnd,out⟩

#print axioms generated_rootApply
end Maxwell.Continuum.Calibration.SeedRoot
