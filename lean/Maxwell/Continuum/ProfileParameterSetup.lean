import Maxwell.Continuum.ProfileRuntimeDimensionsExecution
import Maxwell.Continuum.ProfileDFTInvariant
import Maxwell.Continuum.DyadicFloorPowerPreparation

/-! Runtime metadata and the stored dyadic scale for the literal profile
producer. The program contains only fixed small literals. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def parameterIds : Finset ℕ := {145,640,652,653,661,663,664,667,668,669}
def parameterWorkspace : Finset ℕ := {0,1,2,3,144,146}∪parameterIds
def parameterInput (D P grid i : ℕ) : ℕ :=
  if i=661 then D else if i=663 then P else if i=664 then grid else 0
def parameterInstructions : List NatAssign.Instruction :=
  [.literal 667 1,.copy 663 668,.literal 669 4,.add 669 668,
   .copy 661 669,.add 667 669,.copy 669 652,.copy 663 653,.copy 668 640,.copy 663 145]
def parameterValues (D P grid : ℕ) : ℕ→ℕ := NatAssign.values parameterInstructions (parameterInput D P grid)
def parameterCode : Code := .seq (NatAssign.code parameterInstructions) DyadicFloor.StoredPower.powerCode
def parameterCost (P W : ℕ) : ℕ := stageCost W+2^10*(P+2)^2

theorem parameterInstructions_valid : ∀a∈parameterInstructions,a.Valid parameterIds := by
  simp [parameterInstructions,NatAssign.Instruction.Valid,parameterIds]

theorem parameterValues_eq (D P grid i : ℕ) : parameterValues D P grid i=
    if i=145 then P else if i=640 then P+4 else if i=652 then D+1 else if i=653 then P
    else if i=667 then 1 else if i=668 then P+4 else if i=669 then D+1
    else parameterInput D P grid i := by
  simp [parameterValues,parameterInstructions,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,parameterInput,Function.update_apply]
  split_ifs <;> simp_all [Nat.add_comm]

theorem parameters_executes (D P grid W : ℕ) (hW : 3≤W)
    (hD : D.bits.length≤W) (hP : P.bits.length≤W) (hg : grid.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank parameterIds (parameterInput D P grid) s.val) (hz : NatAssign.Scratch s.val)
    (h144 : Blank s.val 144) (h146 : Blank s.val 146) :
    ∃cost t,Executes input tape parameterCode cost s t ∧ cost≤parameterCost P W ∧
      DFTParameters D P t ∧ Word t.val 144 (2^P) ∧ Word t.val 661 D ∧ Word t.val 664 grid ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame parameterWorkspace s.val t.val := by
  have width (i : ℕ) (_hi : i∈parameterIds) : (parameterInput D P grid i).bits.length≤W := by
    unfold parameterInput
    split_ifs <;> first | exact hD | exact hP | exact hg | simp
  obtain ⟨c0,s0,e0,hc0,b0,z0,f0⟩ := fixedBankStage_executes parameterIds (by
    intro i hi;simp only [parameterIds,Finset.mem_insert,Finset.mem_singleton] at hi;omega)
    parameterInstructions parameterInstructions_valid (by simp [parameterInstructions])
    (parameterInput D P grid) W width (by
      simp [parameterInstructions,NatAssign.Instruction.literalWidth,
        show (4:ℕ).bits.length=3 from rfl]
      omega) input tape s hs hz
  change NatAssign.Bank parameterIds (parameterValues D P grid) s0.val at b0
  have powerInput : Word s0.val 145 P := by simpa [parameterValues_eq] using b0 145 (by decide)
  obtain ⟨c1,t,e1,hc1,_,power,_,f1⟩ := DyadicFloor.StoredPower.power_executes P input tape s0 powerInput
    (blank_of_eq (f0.tapes 146 (by decide)) h146) (blank_of_eq (f0.tapes 144 (by decide)) h144)
  have word (i : ℕ) (hi : i∈parameterIds) : Word t.val i (parameterValues D P grid i) :=
    word_of_eq (f1.tapes i (by
      simp only [parameterIds,Finset.mem_insert,Finset.mem_singleton] at hi
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or];omega)) (b0 i hi)
  refine ⟨c0+c1,t,e0.seq e1,by unfold parameterCost;omega,?_,power,?_,?_,?_,
    (f0.mono (by decide)).trans (f1.mono (by decide))⟩
  · exact ⟨by simpa [parameterValues_eq,parameterInput] using word 663 (by decide),
      by simpa [parameterValues_eq] using word 667 (by decide),
      by simpa [parameterValues_eq] using word 668 (by decide),
      by simpa [parameterValues_eq] using word 669 (by decide),
      by simpa [parameterValues_eq] using word 652 (by decide),
      by simpa [parameterValues_eq] using word 653 (by decide),
      by simpa [parameterValues_eq] using word 640 (by decide)⟩
  · simpa [parameterValues_eq,parameterInput] using word 661 (by decide)
  · simpa [parameterValues_eq,parameterInput] using word 664 (by decide)
  · intro i hi
    exact blank_of_eq (f1.tapes i (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or];omega)) (z0 i hi)

#print axioms parameters_executes
end Maxwell.Continuum.Profile.Runtime
