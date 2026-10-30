import Maxwell.Continuum.RationalDataflowExecution

/-! One fixed natural multiplication accumulates a raw input denominator. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000

def denominatorStep (accumulator entry : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update v accumulator
    ⟨(v entry).denominator*(v accumulator).positive,
     (v accumulator).negative,(v accumulator).denominator⟩

def denominatorStage (accumulator entry : ℕ) : List NatAssign.Instruction :=
  [.multiply (denominatorPort entry) (positivePort accumulator)]

theorem denominatorStage_valid (S : Finset ℕ) (accumulator entry : ℕ)
    (ha : accumulator∈S) (he : entry∈S) :
    ∀ ins∈denominatorStage accumulator entry, ins.Valid (ids S) := by
  have hp := cell_mem ha (show positivePort accumulator∈cellPorts accumulator by simp [cellPorts])
  have hd := cell_mem he (show denominatorPort entry∈cellPorts entry by simp [cellPorts])
  simp [denominatorStage,NatAssign.Instruction.Valid,hp,hd]

theorem denominatorStage_values (accumulator entry : ℕ) (v : ℕ→Parts) :
    NatAssign.values (denominatorStage accumulator entry) (dataValues v)=
      dataValues (denominatorStep accumulator entry v) := by
  rw [denominatorStep,←writeParts_dataValues]
  simp only [denominatorStage,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,dataValues_denominator,
    dataValues_positive,writeParts]
  ext i
  by_cases hp : i=positivePort accumulator
  · subst i
    simp
  · by_cases hn : i=negativePort accumulator
    · subst i
      simp
    · by_cases hd : i=denominatorPort accumulator
      · subst i
        simp
      · simp [hp,hn,hd]

theorem denominator_executes (S : Finset ℕ) (accumulator entry : ℕ)
    (ha : accumulator∈S) (he : entry∈S) (v : ℕ→Parts) (B : ℕ)
    (hw : ∀ i∈S, (v i).Width B) (input : List Bool) (tape : ℕ→Bool)
    (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape (NatAssign.code (denominatorStage accumulator entry)) cost s t ∧
      cost≤stageCost B ∧ Ready S (denominatorStep accumulator entry v) t ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨cost,t,hex,hcost,hbank,hscratch,hframe⟩ := fixedStage_executes S
    (denominatorStage accumulator entry) (denominatorStage_valid S accumulator entry ha he)
    (by simp [denominatorStage]) (dataValues v) B (dataValues_width S v B hw)
    (by simp [denominatorStage,NatAssign.Instruction.literalWidth]) input tape s hs.1 hs.2
  rw [denominatorStage_values] at hbank
  exact ⟨cost,t,hex,hcost,⟨hbank,hscratch⟩,hframe⟩

#print axioms denominator_executes
end Maxwell.Continuum.RationalDataflow
