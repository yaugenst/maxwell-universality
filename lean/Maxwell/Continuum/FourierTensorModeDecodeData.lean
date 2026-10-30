import Maxwell.Continuum.FourierTensorModeReads
import Maxwell.Continuum.FourierTensorDecodeScratch

/-! The alias decoder and rational row bank share one explicitly assembled
runtime bank. The quotient scratch values are actual zeros. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeDecode
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def allIds : Finset ℕ := (ModeIndex.ports∪ids RowArithmetic.bank)∪NaturalQuotient.workPorts
def changed : Finset ℕ := {0,1,2,3,4}∪allIds
def combined (v : ℕ→Parts) (n : ℕ→ℕ) (i : ℕ) : ℕ :=
  if i∈ModeIndex.ports then n i else dataValues v i
def after (v : ℕ→Parts) (n : ℕ→ℕ) : ℕ→ℕ :=
  NatAssign.values ArrayDecodeMachine.coordinateLoad (ArrayDecodeMachine.output (combined v n))
def decoded (v : ℕ→Parts) (n : ℕ→ℕ) : ℕ→Parts :=
  ArrayDecodeMachine.loadedParts v (ArrayDecodeMachine.output (combined v n))

theorem allIds_ge (i : ℕ) (hi : i∈allIds) : 10 ≤ i := by
  rcases Finset.mem_union.mp hi with hi|hi
  · rcases Finset.mem_union.mp hi with hi|hi
    · simp only [ModeIndex.ports,Finset.mem_Icc] at hi;omega
    · exact ids_ge_ten RowArithmetic.bank i hi
  · simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi;omega

theorem decode_subset : ArrayDecodeMachine.ports⊆allIds := by
  intro i hi
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  simp only [ArrayDecodeMachine.ports,Finset.mem_Icc] at hi
  simp only [ModeIndex.ports,Finset.mem_Icc]
  omega

theorem parts_outside (i : ℕ) (hi : i∈ids RowArithmetic.bank) : i∉ModeIndex.ports := by
  intro hp
  simp only [ModeIndex.ports,Finset.mem_Icc] at hp
  exact outside_workspace RowArithmetic.bank i (by omega) (Finset.mem_union_right _ hi)

theorem combined_parts (v : ℕ→Parts) (n : ℕ→ℕ) (i : ℕ) (hi : i∈ids RowArithmetic.bank) :
    combined v n i=dataValues v i := by simp only [combined,ite_eq_right (parts_outside i hi)]

theorem combined_quotient (v : ℕ→Parts) (n : ℕ→ℕ) (i : ℕ)
    (hi : i∈NaturalQuotient.workPorts) : combined v n i=0 := by
  have hlo : i<310 := by simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  have hp : i∉ModeIndex.ports := by simp only [ModeIndex.ports,Finset.mem_Icc];omega
  rw [combined,ite_eq_right hp,dataValues_small v (by omega)]

theorem combined_bank {v : ℕ→Parts} {n : ℕ→ℕ} {s : Store}
    (hv : RationalDataflow.Ready RowArithmetic.bank v s) (hn : NatAssign.Bank ModeIndex.ports n s.val)
    (hz : DyadicFloor.Clean s.val) : NatAssign.Bank allIds (combined v n) s.val := by
  intro i hi
  by_cases hp : i∈ModeIndex.ports
  · simpa only [combined,ite_eq_left hp] using hn i hp
  · rcases Finset.mem_union.mp hi with hi|hi
    · have hr := (Finset.mem_union.mp hi).resolve_left hp
      simpa only [combined_parts v n i hr] using hv.1 i hr
    · rw [combined_quotient v n i hi]
      exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (hz.2 i (Finset.mem_union_right _ hi))

theorem combined_width (v : ℕ→Parts) (n : ℕ→ℕ) (W : ℕ)
    (hv : WidthBank RowArithmetic.bank W v) (hn : ∀i∈ModeIndex.ports,(n i).bits.length≤W) :
    ∀i∈allIds,(combined v n i).bits.length≤W := by
  intro i hi
  by_cases hp : i∈ModeIndex.ports
  · simpa only [combined,ite_eq_left hp] using hn i hp
  · rcases Finset.mem_union.mp hi with hi|hi
    · have hr := (Finset.mem_union.mp hi).resolve_left hp
      rw [combined_parts v n i hr]
      exact dataValues_width RowArithmetic.bank v W hv i hr
    · rw [combined_quotient v n i hi];simp

theorem coordinateLoad_low (n : ℕ→ℕ) (i : ℕ) (hi : i<1000) :
    NatAssign.values ArrayDecodeMachine.coordinateLoad n i=n i := by
  rw [ArrayDecodeMachine.coordinateLoad_values]
  simp (disch := omega) only [writeParts,positivePort,negativePort,denominatorPort,
    Function.update_of_ne]

theorem after_quotient (v : ℕ→Parts) (n : ℕ→ℕ) (i : ℕ) (hi : i∈NaturalQuotient.workPorts) :
    after v n i=0 := by
  have hlo : i<310 := by simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  rw [after,coordinateLoad_low _ i (by omega),ArrayDecodeMachine.output_outside _ i
    (by simp only [ArrayDecodeMachine.ports,Finset.mem_Icc];omega),combined_quotient v n i hi]

theorem after_width (v : ℕ→Parts) (n : ℕ→ℕ) (W : ℕ)
    (hv : WidthBank RowArithmetic.bank W v) (hn : ∀i∈ModeIndex.ports,(n i).bits.length≤W) :
    ∀i∈ModeIndex.ports,(after v n i).bits.length≤2*W+8 := by
  intro i hi
  have hh : i<1000 := by simp only [ModeIndex.ports,Finset.mem_Icc] at hi;omega
  rw [after,coordinateLoad_low _ i hh]
  exact ArrayDecodeMachine.output_width (combined v n) allIds decode_subset W (combined_width v n W hv hn)
    i (Finset.mem_union_left _ (Finset.mem_union_left _ hi))

theorem decoded_width (v : ℕ→Parts) (n : ℕ→ℕ) (W : ℕ)
    (hv : WidthBank RowArithmetic.bank W v) (hn : ∀i∈ModeIndex.ports,(n i).bits.length≤W) :
    WidthBank RowArithmetic.bank (2*W+8) (decoded v n) := by
  apply ArrayDecodeMachine.loadedParts_width v _ _ (by omega) (hv.mono (by omega))
  intro i hi
  exact ArrayDecodeMachine.output_width (combined v n) allIds decode_subset W (combined_width v n W hv hn)
    i (decode_subset hi)

theorem decoded_good (v : ℕ→Parts) (n : ℕ→ℕ) (hg : Good RowArithmetic.bank v) :
    Good RowArithmetic.bank (decoded v n) := ArrayDecodeMachine.loadedParts_good v _ hg

#print axioms combined_bank
#print axioms decoded_width
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeDecode
