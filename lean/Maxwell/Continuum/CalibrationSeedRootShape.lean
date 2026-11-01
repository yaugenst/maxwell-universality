import Maxwell.Continuum.CalibrationSeedRootDestination

/-! The seed cube side, row count, real dimension, and doubled storage
count are computed from the retained supercell size and root degree. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

def shapeWidth (B : ℕ) : ℕ := 2^shapePlan.length*(B+1)
def shapeCost (B : ℕ) : ℕ := 3000*8^shapePlan.length*(B+2)^2

theorem shape_executes {T : ℕ} (a : PartArray.Table T) (allIds : Finset ℕ)
    (lower : ∀i∈allIds,4 ≤ i) (includes : ids⊆allIds)
    (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ) (hB : 2≤B)
    (width : ∀i∈allIds,(n i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank allIds n s.val) (ready : Ready slots v s) (cache : a.Ready s) :
    ∃cost t,Executes input tape (NatAssign.code shapePlan) cost s t ∧
      cost≤shapeCost B ∧ NatAssign.Bank allIds (shapeValues n) t.val ∧
      (∀i∈allIds,(shapeValues n i).bits.length≤shapeWidth B) ∧
      Ready slots v t ∧ a.Ready t ∧ BinaryPrecision.Frame workspace s.val t.val := by
  have valid : ∀x∈shapePlan,x.Valid allIds := by
    intro x hx
    have h:=shapePlan_valid x hx
    cases x <;> simp only [NatAssign.Instruction.Valid] at h ⊢
    · exact includes h
    all_goals exact ⟨includes h.1,includes h.2.1,h.2.2⟩
  obtain ⟨cost,t,e,hc,nt,zt,f⟩ := NatAssign.executes allIds lower shapePlan valid
    n input tape s bank ready.2
  have fw : BinaryPrecision.Frame workspace s.val t.val :=
    f.mono (NatAssign.changes_subset ids _ shapePlan_valid)
  have magnitude (i : ℕ) (hi : i∈RationalMagnitude.ids) : RationalAccumulator.Word t.val i 0 := by
    have lo : i<1000 := by
      simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    have hword := ready.1 i (Finset.mem_union_right _ (Finset.mem_union_right _ hi))
    rw [dataValues_small v lo] at hword
    apply RationalAccumulator.word_of_eq (f.tapes i _) hword
    simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    simp [NatAssign.changes,shapePlan,NatAssign.Instruction.target]
    omega
  have literals : ∀x∈shapePlan,x.literalWidth≤B := by
    simp [shapePlan,NatAssign.Instruction.literalWidth,
      show (2:ℕ).bits.length=2 by decide,show (3:ℕ).bits.length=2 by decide]
    omega
  have price := NatAssign.price_bound allIds _ valid n B width literals
  have bound : ∀i∈allIds,(shapeValues n i).bits.length≤shapeWidth B := by
    intro i hi
    have hh := NatAssign.values_width allIds _ valid n B width literals i hi
    exact (Nat.le_add_right _ 1).trans hh
  exact ⟨cost,t,e,hc.trans price,nt,bound,rational_ready_after_control ready fw zt magnitude,
    table_ready_after_control cache fw zt,fw⟩

#print axioms shape_executes
end Maxwell.Continuum.Calibration.SeedRoot
