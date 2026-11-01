import Maxwell.Continuum.StoredChronologicalWells
import Maxwell.Continuum.RationalDataflowRetainedCells
import Maxwell.Continuum.WellStrengthArithmetic
import Maxwell.Cost.Structured.TapeSet

/-! Reading the completed strength table changes only raw register zero.
The calibrated mode, scale, and other retained cells survive serialization. -/
namespace Maxwell.Continuum.WellPayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

theorem code_retains_raw : WellOutput.code.protectsSet (ports (WellStrength.bank.erase 0))=true:=by decide +kernel

theorem code_retains_rounding : WellOutput.code.protectsSet
    ({4,144}∪DyadicFloor.extraIds∪NaturalQuotient.workPorts)=true:=by decide +kernel

theorem rounding_frame {P cost : ℕ} {input : List Bool} {tape : ℕ→Bool} {s t : Store}
    (run : Executes input tape WellOutput.code cost s t) (clean : DyadicFloor.Clean s.val)
    (power : Word s.val 144 (2^P)) : DyadicFloor.Clean t.val ∧Word t.val 144 (2^P):=by
  have keep (i : ℕ) (hi : i∈({4,144}∪DyadicFloor.extraIds∪NaturalQuotient.workPorts:Finset ℕ)):=
    run.protectsSet _ code_retains_rounding i hi
  refine ⟨⟨blank_of_eq (keep 4 (by decide)) clean.1,?_⟩,word_of_eq (keep 144 (by decide)) power⟩
  intro i hi
  exact blank_of_eq (keep i (by
    simp only [Finset.mem_union] at hi ⊢
    tauto)) (clean.2 i hi)

theorem raw_frame {J P B j : ℕ} {a : PartArray.Table J} {profile template : List Bool}
    {parts values : ℕ→Parts} {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (run : Executes input tape WellOutput.code cost s t)
    (before : Ready WellStrength.bank parts s) (after : State a P B j profile template values t) :
    Ready WellStrength.bank (Function.update parts 0 (values 0)) t:=by
  have beforeCells:=Cells.of_ready before
  have afterCell:=Cells.of_ready after.ready
  have cells : Cells WellStrength.bank (Function.update parts 0 (values 0)) t.val:=by
    intro i hi
    by_cases eq : i=0
    · subst i
      simpa only [Function.update_self] using afterCell 0 (by decide)
    · rw [Function.update_of_ne eq]
      have keep (k : ℕ) (hk : k∈cellPorts i):=
        run.protectsSet (ports (WellStrength.bank.erase 0)) code_retains_raw k
          (Finset.mem_biUnion.mpr ⟨i,Finset.mem_erase.mpr ⟨eq,hi⟩,hk⟩)
      exact ⟨word_of_eq (keep (positivePort i) (by simp [cellPorts])) (beforeCells i hi).1,
        word_of_eq (keep (positivePort i+1) (by simp [cellPorts,positivePort,negativePort])) (beforeCells i hi).2.1,
        word_of_eq (keep (positivePort i+2) (by simp [cellPorts,positivePort,denominatorPort])) (beforeCells i hi).2.2⟩
  apply cells.ready _ after.ready.2
  intro i hi
  have word:=after.ready.1 i (Finset.mem_union_right _ hi)
  have small : i<1000:=by
    simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  rw [dataValues_small values small,zero_word_iff_blank] at word
  exact word

#print axioms raw_frame
end Maxwell.Continuum.WellPayload
