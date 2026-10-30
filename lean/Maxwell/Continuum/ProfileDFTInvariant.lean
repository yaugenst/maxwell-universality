import Maxwell.Continuum.ProfileDFTStepMachine
import Maxwell.Continuum.RationalDataflowNaturalChannels
import Maxwell.Continuum.RationalDataflowSizedCounted
import Maxwell.Continuum.ProfileDFTValidity

/-! The profile transform's literal counted accumulator invariant. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000

def dftLoopWidth (grid U : ℕ) : ℕ := dftScratchWidth U+(grid+1)*(dftTermWidth U+1)+1
def dftAccumulatorWidth (grid remaining U : ℕ) : ℕ := (grid-remaining)*(dftTermWidth U+1)+1
def dftLoopBody : Code := .seq (NaturalChannel.code .positive 201 0) dftStepCode
def dftLoopCode : Code := countedProgram 201 dftLoopBody

structure DFTState (S : Finset ℕ) (grid D P U : ℕ) (k : ℤ) (remaining : ℕ) (s : Store) where
  bound : remaining≤grid
  values : ℕ→Parts
  ready : Ready S values s
  width : WidthBank S (dftLoopWidth grid U) values
  good : Good S values
  argumentNegative : (values 0).negative=0
  argumentDenominator : (values 0).denominator=grid
  frequency : values 5=integerArgument (-k)
  accumulatorValid : (values 9).Valid
  accumulatorWidth : (values 9).Width (dftAccumulatorWidth grid remaining U)
  accumulatorValue : (values 9).value=∑j∈Finset.Ico remaining grid,(dftTerm grid D P k j).value
  phaseClean : Phase.Runtime.Clean s.val
  glueClean : Glue.Clean s.val
  parameters : DFTParameters D P s

def DFTInvariant (S : Finset ℕ) (grid D P U : ℕ) (k : ℤ) (remaining : ℕ) (s : Store) : Prop :=
  Nonempty (DFTState S grid D P U k remaining s)

theorem dftStepValues_zero (D P : ℕ) (v : ℕ→Parts) : dftStepValues D P v 0=v 0 := by
  simp [dftStepValues,dftFinish,dftAfterPhase,dftAfterPreparation,dftPreparation,
    evaluate,Instruction.update,angularValues_zero]
theorem dftStepValues_frequency (D P : ℕ) (v : ℕ→Parts) : dftStepValues D P v 5=v 5 := by
  simp [dftStepValues,dftFinish,dftAfterPhase,dftAfterPreparation,dftPreparation,
    evaluate,Instruction.update,angularValues_large]

theorem DFTParameters.count_frame {D P : ℕ} {s t : Store}
    (h : DFTParameters D P s) (f : CountedShifted.Frame 201 s t) : DFTParameters D P t := by
  exact ⟨word_of_eq (f.2.2.2.2.2.1 663 (by decide)) h.precision,
    word_of_eq (f.2.2.2.2.2.1 667 (by decide)) h.one,
    word_of_eq (f.2.2.2.2.2.1 668 (by decide)) h.guard,
    word_of_eq (f.2.2.2.2.2.1 669 (by decide)) h.range,
    word_of_eq (f.2.2.2.2.2.1 652 (by decide)) h.phaseRange,
    word_of_eq (f.2.2.2.2.2.1 653 (by decide)) h.phasePrecision,
    word_of_eq (f.2.2.2.2.2.1 640 (by decide)) h.gluePrecision⟩

theorem DFTInvariant.count_frame {S : Finset ℕ} {grid D P U : ℕ} {k : ℤ} {r : ℕ} {s t : Store}
    (h : DFTInvariant S grid D P U k r s) (f : CountedShifted.Frame 201 s t) :
    DFTInvariant S grid D P U k r t := by
  obtain ⟨h⟩ := h
  refine ⟨⟨h.bound,h.values,h.ready.count_frame S h.values 201
    (RationalDataflow.outside_workspace S 201 (by decide)) f,h.width,h.good,h.argumentNegative,
    h.argumentDenominator,h.frequency,h.accumulatorValid,h.accumulatorWidth,h.accumulatorValue,?_,?_,h.parameters.count_frame f⟩⟩
  · intro i hi
    apply blank_of_eq (f.2.2.2.2.2.1 i _) (h.phaseClean i hi)
    intro he
    subst i
    exact (show (201:ℕ)∉PhaseMachine.Runtime.ids by decide)
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
  · intro i hi
    apply blank_of_eq (f.2.2.2.2.2.1 i _) (h.glueClean i hi)
    intro he
    subst i
    exact (show (201:ℕ)∉GlueMachine.Runtime.ids by decide) (Finset.mem_of_mem_erase hi)

theorem DFTParameters.channel_frame {D P : ℕ} {s t : Store}
    (h : DFTParameters D P s) (f : BinaryPrecision.Frame {positivePort 0} s.val t.val) :
    DFTParameters D P t := by
  exact ⟨word_of_eq (f.tapes 663 (by decide)) h.precision,
    word_of_eq (f.tapes 667 (by decide)) h.one,word_of_eq (f.tapes 668 (by decide)) h.guard,
    word_of_eq (f.tapes 669 (by decide)) h.range,word_of_eq (f.tapes 652 (by decide)) h.phaseRange,
    word_of_eq (f.tapes 653 (by decide)) h.phasePrecision,word_of_eq (f.tapes 640 (by decide)) h.gluePrecision⟩

theorem argument_counter_replace (v : ℕ→Parts) (grid j : ℕ)
    (hn : (v 0).negative=0) (hd : (v 0).denominator=grid) :
    NaturalChannel.replace .positive (v 0) j=gridArgument grid j := by
  simp only [NaturalChannel.replace,gridArgument,hn,hd]

#print axioms DFTInvariant.count_frame
end Maxwell.Continuum.Profile.Runtime
