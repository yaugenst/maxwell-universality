import Maxwell.Continuum.PhaseRuntimeDataflowLoaded
import Maxwell.Continuum.ChebyshevWaveLocalWidths

/-! Fixed runtime preparation of the nested wave-sample range and precision.
All ten metadata words are ordinary stored inputs or charged outputs. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def parameterIds : Finset ℕ := {670,671,672,673,674,675,676,677,678,679}
def initialParameters (Q P i : ℕ) : ℕ := if i=670 then Q else if i=671 then P else 0
def scannedParameters (Q P : ℕ) : ℕ→ℕ := Function.update (initialParameters Q P) 678 Q.bits.length
def parameterInstructions : List NatAssign.Instruction :=
  [.literal 672 1,.copy 670 673,.add 672 673,.literal 676 2,.multiply 676 673,
   .copy 671 674,.literal 677 4,.add 677 674,.copy 674 675,.add 678 675,.add 677 675]
def parameterValues (Q P : ℕ) : ℕ→ℕ := NatAssign.values parameterInstructions (scannedParameters Q P)
def parameterCode : Code := .seq (WordLength.code 670 678) (NatAssign.code parameterInstructions)
def Parameters (Q P : ℕ) (s : Store) : Prop := NatAssign.Bank parameterIds (parameterValues Q P) s.val

theorem parameterIds_range (i : ℕ) (hi : i∈parameterIds) : 670 ≤ i ∧ i≤679 := by
  simp only [parameterIds,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem parameterInstructions_valid : ∀a∈parameterInstructions,a.Valid parameterIds := by
  simp [parameterInstructions,NatAssign.Instruction.Valid,parameterIds]

theorem parameterValues_eq (Q P i : ℕ) : parameterValues Q P i=
    if i=672 then 1 else if i=673 then 2*(Q+1) else if i=674 then P+4 else
    if i=675 then Calibration.phaseBits Q (P+4) else if i=676 then 2 else
    if i=677 then 4 else scannedParameters Q P i := by
  simp (disch := omega) [parameterValues,parameterInstructions,scannedParameters,initialParameters,
    NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    Calibration.phaseBits,PhaseMachine.Runtime.clog_two_succ,Function.update_apply]
  split_ifs <;> omega

theorem parameterValues_width (Q P i : ℕ) : (parameterValues Q P i).bits.length≤2*Q+P+12 := by
  have hb := Machin.Runtime.nat_bits_le_self Q
  have hv : parameterValues Q P i≤2*Q+P+12 := by
    rw [parameterValues_eq]
    simp only [scannedParameters,initialParameters,Calibration.phaseBits,Function.update_apply]
    rw [PhaseMachine.Runtime.clog_two_succ]
    split_ifs <;> omega
  exact (Machin.Runtime.nat_bits_le_self _).trans hv

theorem Parameters.phase_frame {Q P : ℕ} {S : Finset ℕ} {s t : Store} (h : Parameters Q P s)
    (f : BinaryPrecision.Frame (Phase.Runtime.workspace S) s.val t.val) : Parameters Q P t := by
  intro i hi
  have hr := parameterIds_range i hi
  exact word_of_eq (f.tapes i (Phase.Runtime.metadata_outside_workspace S i (by omega))) (h i hi)

theorem Parameters.arithmetic_frame {Q P : ℕ} {S : Finset ℕ} {s t : Store} (h : Parameters Q P s)
    (f : BinaryPrecision.Frame (RationalDataflow.workspace S) s.val t.val) : Parameters Q P t := by
  intro i hi
  have hr := parameterIds_range i hi
  exact word_of_eq (f.tapes i (RationalDataflow.outside_workspace S i (by omega))) (h i hi)

theorem Parameters.inner {Q P : ℕ} {s : Store} (h : Parameters Q P s) :
    Word s.val 672 1 ∧ Word s.val 675 (Calibration.phaseBits Q (P+4)) := by
  constructor
  · simpa only [parameterValues_eq,ite_true] using h 672 (by decide)
  · simpa only [parameterValues_eq,show (675:ℕ)≠672 by decide,show (675:ℕ)≠673 by decide,
      show (675:ℕ)≠674 by decide,ite_false,ite_true] using h 675 (by decide)

theorem Parameters.outer {Q P : ℕ} {s : Store} (h : Parameters Q P s) :
    Word s.val 673 (2*(Q+1)) ∧ Word s.val 674 (P+4) := by
  constructor
  · simpa only [parameterValues_eq,show (673:ℕ)≠672 by decide,ite_false,ite_true] using h 673 (by decide)
  · simpa only [parameterValues_eq,show (674:ℕ)≠672 by decide,show (674:ℕ)≠673 by decide,
      ite_false,ite_true] using h 674 (by decide)

#print axioms parameterValues_eq
#print axioms parameterValues_width
end Maxwell.Continuum.Profile.WaveMachine.Runtime
