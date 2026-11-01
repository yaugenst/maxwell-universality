import Maxwell.Continuum.CalibrationSeedDenominatorMachine

/-! Actual natural products materialize all three unreduced seed components.
The rational signs are represented by separate nonnegative channels. -/
namespace Maxwell.Continuum.Calibration.SeedMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000

def componentsPlan : List NatAssign.Instruction :=
  [.copy 32 714,.copy 548 715,.literal 716 8,.literal 717 15,.literal 718 6,.literal 719 10,.literal 729 7,
   .copy 703 720,.multiply 716 720,.add 702 720,.multiply 715 720,.literal 721 0,
   .copy 703 722,.multiply 714 722,.multiply 717 722,
   .copy 703 723,.multiply 715 723,.copy 702 724,.multiply 715 724,
   .copy 703 725,.multiply 714 725,.multiply 718 725,
   .copy 702 726,.multiply 715 726,.copy 703 727,.multiply 729 727,.multiply 715 727,
   .copy 703 728,.multiply 714 728,.multiply 719 728]
def componentsValues (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values componentsPlan v
def storedComponent (v : ℕ→ℕ) (j : Fin 3) : Parts :=
  ⟨v (720+3*j.val),v (721+3*j.val),v (722+3*j.val)⟩
def componentsWidth (B : ℕ) : ℕ := 2^componentsPlan.length*(B+5)
def componentsCost (B : ℕ) : ℕ := 3000*8^componentsPlan.length*(B+6)^2

theorem componentsPlan_valid : ∀a∈componentsPlan,a.Valid componentIds := by
  simp [componentsPlan,NatAssign.Instruction.Valid,componentIds,savedIds]
theorem components_values (v : ℕ→ℕ) (j : Fin 3) :
    storedComponent (componentsValues v) j=componentParts (v 702) (v 703) (v 32) (v 548) j := by
  fin_cases j <;>
    simp [storedComponent,componentsValues,componentsPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,componentParts,Parts.mk.injEq]
  all_goals (ring_nf;trivial)

theorem components_executes (v : ℕ→ℕ) (B : ℕ) (width : ∀i∈componentIds,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank componentIds v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (NatAssign.code componentsPlan) cost s t ∧ cost≤componentsCost B ∧
      NatAssign.Bank componentIds (componentsValues v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈componentIds,(componentsValues v i).bits.length≤componentsWidth B) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have literals : ∀a∈componentsPlan,a.literalWidth≤B+4 := by
    simp [componentsPlan,NatAssign.Instruction.literalWidth,
      show (8:ℕ).bits.length=4 by decide,show (15:ℕ).bits.length=4 by decide,
      show (6:ℕ).bits.length=3 by decide,show (10:ℕ).bits.length=4 by decide,
      show (7:ℕ).bits.length=3 by decide]
  obtain ⟨cost,t,execution,bound,bt,st,frame⟩ := NatAssign.executes componentIds
    (fun i hi=>ids_ge i (componentIds_subset hi)) componentsPlan componentsPlan_valid v input tape s bank scratch
  have price := NatAssign.price_bound componentIds componentsPlan componentsPlan_valid v (B+4)
    (fun i hi=>(width i hi).trans (by omega)) literals
  refine ⟨cost,t,execution,bound.trans price,bt,st,?_,frame.mono (by decide+kernel)⟩
  intro i hi
  have h := NatAssign.values_width componentIds componentsPlan componentsPlan_valid v (B+4)
    (fun i hi=>(width i hi).trans (by omega)) literals i hi
  exact (Nat.le_add_right _ 1).trans h

#print axioms components_executes
end Maxwell.Continuum.Calibration.SeedMachine
