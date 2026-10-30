import Maxwell.Continuum.ChebyshevWaveRuntimeEncoded
import Maxwell.Continuum.RationalDataflowNaturalChannels

/-! The small input bank is reconstructed for every coefficient of the wave
cache. Only the four fixed frequency/grid entries survive between passes. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def cacheMetadata : Finset ℕ := {10,11,14,15}
def SameMetadata (v w : ℕ→Parts) : Prop := ∀i∈cacheMetadata,v i=w i
def cacheResetInstructions : List RationalDataflow.Instruction :=
  [.literal 0 0,.literal 1 0,.literal 2 0,.literal 3 0,.literal 4 0,
   .literal 5 0,.literal 6 0,.literal 7 0,.literal 8 0,.literal 9 0,
   .literal 12 0,.literal 13 0]
def cacheResetValues (v : ℕ→Parts) : ℕ→Parts := evaluate cacheResetInstructions v
def cacheLoaded (j : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (cacheResetValues v) 12 ⟨j,0,1⟩

theorem cacheResetInstructions_valid : ∀a∈cacheResetInstructions,a.Valid ids := by
  simp [cacheResetInstructions,RationalDataflow.Instruction.Valid,ids]

theorem cacheResetValues_eq (v : ℕ→Parts) (i : ℕ) :
    cacheResetValues v i=if i<10 ∨ i=12 ∨ i=13 then Parts.literal 0 else v i := by
  by_cases hi : i<14
  · interval_cases i <;>
      simp [cacheResetValues,cacheResetInstructions,evaluate,RationalDataflow.Instruction.update]
  · simp (disch := omega) [cacheResetValues,cacheResetInstructions,evaluate,
      RationalDataflow.Instruction.update,show ¬(i<10 ∨ i=12 ∨ i=13) by omega]

theorem cacheLoaded_eq (j : ℕ) (v : ℕ→Parts) (i : ℕ) :
    cacheLoaded j v i=if i=12 then ⟨j,0,1⟩ else if i<10 ∨ i=13 then Parts.literal 0 else v i := by
  by_cases hi : i=12
  · simp [cacheLoaded,hi]
  · simp [cacheLoaded,cacheResetValues_eq,hi]

theorem cacheLoaded_metadata (j : ℕ) (v : ℕ→Parts) : SameMetadata (cacheLoaded j v) v := by
  intro i hi
  simp only [cacheMetadata,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl <;> simp [cacheLoaded_eq]

theorem cacheLoaded_width (j W : ℕ) (v base : ℕ→Parts) (hm : SameMetadata v base)
    (hw : WidthBank ids W base) (hW : 1 ≤ W) (hj : j.bits.length ≤ W) :
    WidthBank ids W (cacheLoaded j v) := by
  intro i hi
  have hil : i<16 := Finset.mem_range.mp hi
  rw [cacheLoaded_eq]
  split_ifs with he he
  · exact ⟨hj,by simp,by simpa using hW⟩
  · exact (show (Parts.literal 0).Width 1 by unfold Parts.Width Parts.literal;decide).mono hW
  · rw [hm i (by simp only [cacheMetadata,Finset.mem_insert,Finset.mem_singleton];omega)]
    exact hw i hi

theorem cacheLoaded_good (j : ℕ) (v base : ℕ→Parts) (hm : SameMetadata v base)
    (hg : Good ids base) : Good ids (cacheLoaded j v) := by
  intro i hi
  have hil : i<16 := Finset.mem_range.mp hi
  rw [cacheLoaded_eq]
  split_ifs with he he
  · exact Nat.zero_lt_one
  · exact Parts.literal_valid 0
  · rw [hm i (by simp only [cacheMetadata,Finset.mem_insert,Finset.mem_singleton];omega)]
    exact hg i hi

theorem cacheLoaded_input (grid j : ℕ) (q : ℚ) (v base : ℕ→Parts)
    (hm : SameMetadata v base) (hi : SumInput grid q 0 0 base) :
    SumInput grid q (j:ℤ) 0 (cacheLoaded j v) := by
  have keep (i : ℕ) (hi : i∈cacheMetadata) := (cacheLoaded_metadata j v i hi).trans (hm i hi)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [keep 10 (by decide)];exact hi.frequency
  · rw [keep 11 (by decide)];exact hi.reciprocal
  · simp [cacheLoaded_eq,Parts.value]
  · simp [cacheLoaded_eq,Parts.literal_value]
  · rw [keep 14 (by decide)];exact hi.negativeOne
  · rw [keep 15 (by decide)];exact hi.one

theorem encodedValues_metadata (Q P grid : ℕ) (v : ℕ→Parts) :
    SameMetadata (encodedValues Q P grid v) v := by
  intro i hi
  have h10 : 10 ≤ i := by simp only [cacheMetadata,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  have h12 : i≠12 := by simp only [cacheMetadata,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  have h13 : i≠13 := by simp only [cacheMetadata,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  simp only [encodedValues,canonicalPairValues,roundPairValues,
    Function.update_of_ne (by omega : i≠8),Function.update_of_ne (by omega : i≠9)]
  have hf (w : ℕ→Parts) : finishControl.evaluate w i=w i := by
    simp only [finishControl,finishInstructions,halveControl,Control.prepend,
      List.foldr_cons,List.foldr_nil,Control.evaluate]
    split_ifs <;>
      simp (disch := omega) [RationalDataflow.Instruction.update]
  rw [cosineValues,hf]
  simp only [pairedValues,Function.update_of_ne (by omega : i≠3),
    Function.update_of_ne (by omega : i≠2),secondValues,
    coefficientValues_unchanged_high Q P grid _ i h10 h13]
  simp only [restartValues_eq,h12,ite_false,show ¬(i<10 ∨ i=13) by omega,
    coefficientValues_unchanged_high Q P grid _ i h10 h13]

theorem cacheLoaded_counter (j : ℕ) (v : ℕ→Parts) : cacheLoaded j v 13=⟨0,0,1⟩ := by
  simp [cacheLoaded_eq,Parts.literal]
theorem cacheLoaded_one (j : ℕ) (v base : ℕ→Parts) (hm : SameMetadata v base)
    (h : base 15=⟨1,0,1⟩) : cacheLoaded j v 15=⟨1,0,1⟩ :=
  ((cacheLoaded_metadata j v 15 (by decide)).trans (hm 15 (by decide))).trans h
theorem cacheLoaded_zero (j : ℕ) (v : ℕ→Parts) (i : ℕ) (hi : i<10) :
    (cacheLoaded j v i).value=0 := by
  simp [cacheLoaded_eq,hi,show i≠12 by omega,Parts.literal_value]

#print axioms cacheLoaded_width
#print axioms encodedValues_metadata
end Maxwell.Continuum.Profile.WaveMachine.Runtime
