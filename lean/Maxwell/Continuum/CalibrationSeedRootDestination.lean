import Maxwell.Continuum.CalibrationSeedRootLayout
import Maxwell.Continuum.CalibrationSeedRootEmission

/-! Compute the canonical destination index from the stored row and cube
dimension, preserving the actual seed bank and both array descriptors. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

def destinationWidth (B : ℕ) : ℕ := 2^9*(B+1)
def destinationCost (B : ℕ) : ℕ := 3000*8^9*(B+2)^2

theorem destination_executes {T U : ℕ} (a : PartArray.Table T) (b : PartArray.Table U)
    (j : Fin 3) (part : Fin 2) (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ) (hB : 2≤B)
    (width : ∀i∈rowIds,(n i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank rowIds n s.val) (ready : Ready slots v s)
    (cache : a.Ready s) (output : b.OutputReady s) :
    ∃cost t,Executes input tape (NatAssign.code (destinationPlan j part)) cost s t ∧
      cost≤destinationCost B ∧ NatAssign.Bank rowIds (destinationValues j part n) t.val ∧
      (∀i∈rowIds,(destinationValues j part n i).bits.length≤destinationWidth B) ∧
      Ready slots v t ∧ a.Ready t ∧ b.OutputReady t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have valid : ∀x∈destinationPlan j part,x.Valid rowIds := by
    simp [destinationPlan,NatAssign.Instruction.Valid,rowIds,ids,extra,SelectedParameters.Compare.ids]
  obtain ⟨cost,t,e,hc,nt,zt,f⟩ := NatAssign.executes rowIds
    (fun i hi=>(by decide : 4≤10).trans (rowIds_lower i hi)) (destinationPlan j part) valid
    n input tape s bank ready.2
  have fw : BinaryPrecision.Frame workspace s.val t.val :=
    f.mono (NatAssign.changes_subset ids _ (destinationPlan_valid j part))
  have magnitude (i : ℕ) (hi : i∈RationalMagnitude.ids) : RationalAccumulator.Word t.val i 0 := by
    have lo : i<1000 := by
      simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    have hword := ready.1 i (Finset.mem_union_right _ (Finset.mem_union_right _ hi))
    rw [dataValues_small v lo] at hword
    apply RationalAccumulator.word_of_eq (f.tapes i _) hword
    simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    simp [NatAssign.changes,destinationPlan,NatAssign.Instruction.target]
    omega
  have rt := rational_ready_after_control ready fw zt magnitude
  have ta := table_ready_after_control cache fw zt
  have tb := output_ready_after_terms output ta (Frame.natural fw)
  have literals : ∀x∈destinationPlan j part,x.literalWidth≤B := by
    fin_cases j <;> fin_cases part <;>
      simp [destinationPlan,NatAssign.Instruction.literalWidth,
        show (2:ℕ).bits.length=2 by decide,
        show (3:ℕ).bits.length=2 by decide] <;> omega
  have price := NatAssign.price_bound rowIds _ valid n B width literals
  have bound : ∀i∈rowIds,(destinationValues j part n i).bits.length≤destinationWidth B := by
    intro i hi
    have hh := NatAssign.values_width rowIds _ valid n B width literals i hi
    exact (Nat.le_add_right _ 1).trans hh
  exact ⟨cost,t,e,hc.trans price,nt,bound,rt,ta,tb,fw⟩

#print axioms destination_executes
end Maxwell.Continuum.Calibration.SeedRoot
