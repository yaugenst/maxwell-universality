import Maxwell.Continuum.FourierTensorTraversalData
import Maxwell.Continuum.FourierTensorModeTable

/-! The five additional tensor registers are initialized by actual
denominator writes. Their zero numerators come from the cleared workspace. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorRegisters
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def ports : Finset ℕ := Finset.Icc 1084 1098
def denominators : Finset ℕ := {1086,1089,1092,1095,1098}
def changed : Finset ℕ := {0,1,2,3}∪ports
def plan : List NatAssign.Instruction :=
  [.literal 1086 1,.literal 1089 1,.literal 1092 1,.literal 1095 1,.literal 1098 1]
def code : Code := NatAssign.code plan
def values (v : ℕ→Parts) (i : ℕ) : Parts := if 28 ≤ i then Parts.literal 0 else ModePrepare.canonical v i
def words (i : ℕ) : ℕ := if i∈denominators then 1 else 0

theorem plan_values : NatAssign.values plan (fun _ => 0)=words := by
  funext i
  simp [plan,words,denominators,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_apply]
  split_ifs <;> omega

theorem width (v : ℕ→Parts) (W : ℕ) (hW : 1≤W)
    (hw : WidthBank RowArithmetic.bank W v) : WidthBank termBank W (values v) := by
  intro i hi
  by_cases hh : 28 ≤ i
  · simp only [values,ite_eq_left hh]
    exact (show (Parts.literal 0).Width 1 by norm_num [Parts.Width,Parts.literal]).mono hW
  · simp only [values,ite_eq_right hh]
    exact ModePrepare.canonical_width v W hW hw i (Finset.mem_range.mpr (by omega))

theorem executes (v : ℕ→Parts) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready RowArithmetic.bank (ModePrepare.canonical v) s)
    (hb : ∀i∈ports,Blank s.val i) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤2^100 ∧
      Ready termBank (values v) t ∧ Word t.val 1048 0 ∧ BinaryPrecision.Frame changed s.val t.val := by
  have bank : NatAssign.Bank ports (fun _ => 0) s.val := by
    intro i hi
    exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (hb i hi)
  obtain ⟨cost,t,e,hc,bt,zt,ft⟩ := fixedBankStage_executes ports
    (fun i hi => by have := (Finset.mem_Icc.mp hi).1;omega) plan
    (by simp [plan,NatAssign.Instruction.Valid,ports]) (by decide) (fun _ => 0) 1
    (by simp) (by simp [plan,NatAssign.Instruction.literalWidth]) input tape s bank hr.2
  rw [plan_values] at bt
  have keep (i : ℕ) (hi : i∈RationalDataflow.ids RowArithmetic.bank) :
      t.val.tapes i=s.val.tapes i :=
    ft.tapes i (Finset.disjoint_left.mp
      (by decide : Disjoint (RationalDataflow.ids RowArithmetic.bank) changed) hi)
  have ready : Ready termBank (values v) t := by
    refine ⟨?_,zt⟩
    intro i hi
    rcases Finset.mem_union.mp hi with hcell|hwork
    · obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hcell
      have hjmax : j≤32 := by
        simp only [termBank,tensorBank,WaveMachine.ids,Finset.mem_insert,Finset.mem_union,
          Finset.mem_range,Finset.mem_Ico] at hj
        omega
      by_cases hlow : j<28
      · have hrow : j∈RowArithmetic.bank := Finset.mem_range.mpr hlow
        have word := RationalAccumulator.word_of_eq (keep i (cell_mem hrow hij)) (hr.1 i (cell_mem hrow hij))
        simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hij
        rcases hij with rfl|rfl|rfl <;>
          simpa only [dataValues_positive,dataValues_negative,dataValues_denominator,
            values,show ¬28≤j by omega,ite_false] using word
      · have range : 28≤j ∧ j≤32 := ⟨by omega,hjmax⟩
        have hip : i∈ports := by
          simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hij
          simp only [ports,Finset.mem_Icc,positivePort,negativePort,denominatorPort] at *
          omega
        have word := bt i hip
        have eq : words i=dataValues (values v) i := by
          simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hij
          rcases hij with rfl|rfl|rfl <;>
            simp only [dataValues_positive,dataValues_negative,dataValues_denominator,
              values,ite_eq_left range.1,Parts.literal] <;>
            interval_cases j <;> norm_num [words,denominators,positivePort,negativePort,denominatorPort]
        exact eq ▸ word
    · have him : i∈RationalDataflow.ids RowArithmetic.bank := Finset.mem_union_right _ hwork
      have word := RationalAccumulator.word_of_eq (keep i him) (hr.1 i him)
      have low : i<1000 := by
        simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton] at hwork
        omega
      simpa only [dataValues_small _ low] using word
  have query : Word t.val 1048 0 := by
    have h := RationalAccumulator.word_of_eq (keep 1048 (by decide)) (hr.1 1048 (by decide))
    simpa [dataValues,ModePrepare.canonical,Parts.literal] using h
  exact ⟨cost,t,e,(hc.trans (by norm_num [stageCost])),ready,query,ft⟩

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorRegisters
