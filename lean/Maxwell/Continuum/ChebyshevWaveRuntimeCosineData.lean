import Maxwell.Continuum.ChebyshevWaveRuntimeCoefficient
import Maxwell.Continuum.RationalDataflowStoredPartsClear
import Maxwell.Continuum.RationalDataflowControlResults

/-! Exact raw state of the two Fourier passes producing a cosine coefficient.
The second pass resets the work registers, keeping its phase operand widths
independent of the preceding Fourier accumulator. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def restartInstructions : List RationalDataflow.Instruction :=
  [.literal 0 0,.literal 1 0,.literal 2 0,.literal 3 0,.literal 4 0,
   .literal 5 0,.literal 6 0,.literal 7 0,.literal 8 0,.literal 9 0,
   .literal 13 0,.binary .sub 12 0 12]
def restartValues (v : ℕ→Parts) : ℕ→Parts := evaluate restartInstructions v

theorem restartInstructions_valid : ∀a∈restartInstructions,a.Valid ids := by
  simp [restartInstructions,RationalDataflow.Instruction.Valid,ids]

theorem restartValues_eq (v : ℕ→Parts) (i : ℕ) :
    restartValues v i=if i=12 then ⟨(v i).negative,(v i).positive,(v i).denominator⟩
      else if i<10 ∨ i=13 then Parts.literal 0 else v i := by
  by_cases hi : i<14
  · interval_cases i <;>
      simp [restartValues,restartInstructions,evaluate,RationalDataflow.Instruction.update,
        BinaryOp.eval,Parts.sub,Parts.literal]
  · simp (disch := omega) [restartValues,restartInstructions,evaluate,RationalDataflow.Instruction.update,
      show i≠12 by omega,show ¬(i<10 ∨ i=13) by omega]

theorem coefficientValues_good (Q P grid : ℕ) (v : ℕ→Parts) (hv : Good ids v) :
    Good ids (coefficientValues Q P grid v) :=
  evaluate_good ids normalizeInstructions normalizeInstructions_valid _ (sumValues_good Q P v hv grid)
    (by simp [normalizeInstructions,AdmissibleTrace,RationalDataflow.Instruction.Admissible])

theorem coefficientValues_width (Q P grid W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v)
    (hW : 1 ≤ W) (hgrid : grid.bits.length ≤ W) (hcount : v 13=⟨0,0,1⟩) (hone : v 15=⟨1,0,1⟩) :
    WidthBank ids (16*(sumBankWidth Q P W grid+1)) (coefficientValues Q P grid v) := by
  have hw0 := sumValues_width Q P grid W v hw hW hgrid hcount hone grid le_rfl
  exact (inferred_widthTrace ids normalizeInstructions normalizeInstructions_valid
    (fun _ => sumBankWidth Q P W grid) _ hw0 _ (hw0.mono (by omega))
    (normalize_program_width _)).result

theorem coefficientValues_unchanged_high (Q P grid : ℕ) (v : ℕ→Parts) (i : ℕ)
    (hi : 10 ≤ i) (hne : i≠13) : coefficientValues Q P grid v i=v i := by
  simp only [coefficientValues,normalizeInstructions,evaluate,RationalDataflow.Instruction.update,
    Function.update_of_ne (by omega : i≠8),Function.update_of_ne (by omega : i≠9)]
  exact sumValues_unchanged_high Q P v i hi hne grid

theorem restart_good (v : ℕ→Parts) (hv : Good ids v) : Good ids (restartValues v) :=
  evaluate_good ids restartInstructions restartInstructions_valid v hv
    (by simp [restartInstructions,AdmissibleTrace,RationalDataflow.Instruction.Admissible])

theorem restart_width (Q P grid W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v) (hW : 1 ≤ W) :
    WidthBank ids W (restartValues (coefficientValues Q P grid v)) := by
  intro i hi
  have hi' : i<16 := Finset.mem_range.mp hi
  rw [restartValues_eq]
  split_ifs with he he
  · subst i
    rw [coefficientValues_unchanged_high Q P grid v 12 (by decide) (by decide)]
    exact ⟨(hw 12 (by decide)).2.1,(hw 12 (by decide)).1,(hw 12 (by decide)).2.2⟩
  · simpa only [Parts.Width,Parts.literal,show (0:ℚ).num=0 by rfl,
      show (0:ℚ).den=1 by rfl,Int.neg_zero,Int.toNat_zero,show (0:ℕ).bits.length=0 by decide,
      show (1:ℕ).bits.length=1 by decide] using And.intro (Nat.zero_le W) ⟨Nat.zero_le W,hW⟩
  · rw [coefficientValues_unchanged_high Q P grid v i (by omega) (by omega)]
    exact hw i (Finset.mem_range.mpr hi')

theorem restart_counter (v : ℕ→Parts) : restartValues v 13=⟨0,0,1⟩ := by
  simp [restartValues_eq,Parts.literal]
theorem restart_zero (v : ℕ→Parts) (i : ℕ) (hi : i<10) : (restartValues v i).value=0 := by
  simp [restartValues_eq,show i≠12 by omega,hi,Parts.literal_value]
theorem restart_one (Q P grid : ℕ) (v : ℕ→Parts) (h : v 15=⟨1,0,1⟩) :
    restartValues (coefficientValues Q P grid v) 15=⟨1,0,1⟩ := by
  simp only [restartValues_eq,show ¬(15:ℕ)=12 by decide,show ¬((15:ℕ)<10 ∨ 15=13) by decide,ite_false]
  rw [coefficientValues_unchanged_high Q P grid v 15 (by decide) (by decide),h]

theorem restart_input (Q P grid : ℕ) (q : ℚ) (n : ℤ) (v : ℕ→Parts)
    (hi : SumInput grid q n 0 v) :
    SumInput grid q (-n) 0 (restartValues (coefficientValues Q P grid v)) := by
  have keep (i : ℕ) (h10 : 10 ≤ i) (h12 : i≠12) (h13 : i≠13) :
      restartValues (coefficientValues Q P grid v) i=v i := by
    simp only [restartValues_eq,h12,ite_false,show ¬(i<10 ∨ i=13) by omega]
    exact coefficientValues_unchanged_high Q P grid v i h10 h13
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [keep 10 (by decide) (by decide) (by decide)];exact hi.frequency
  · rw [keep 11 (by decide) (by decide) (by decide)];exact hi.reciprocal
  · rw [restartValues_eq]
    simp only [ite_true,coefficientValues_unchanged_high Q P grid v 12 (by decide) (by decide)]
    have hn : (n:ℚ)=(v 12).value := hi.index.symm
    rw [Int.cast_neg,hn]
    simp only [Parts.value]
    ring
  · rw [restart_counter];simp [Parts.value]
  · rw [keep 14 (by decide) (by decide) (by decide)];exact hi.negativeOne
  · rw [keep 15 (by decide) (by decide) (by decide)];exact hi.one

def secondValues (Q P grid : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  coefficientValues Q P grid (restartValues (coefficientValues Q P grid v))
def pairedValues (Q P grid : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (Function.update (secondValues Q P grid v) 2 (coefficientValues Q P grid v 8))
    3 (coefficientValues Q P grid v 9)
def finishInstructions : List RationalDataflow.Instruction :=
  [.literal 0 0,.binary .sub 12 0 12,.binary .add 8 2 8,.binary .add 9 3 9]
def halveControl : Control := .positive 12 .done
  (.step (.literal 4 (1/2)) (.step (.binary .mul 8 4 8) (.step (.binary .mul 9 4 9) .done)))
def finishControl : Control := halveControl.prepend finishInstructions
def cosineValues (Q P grid : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  finishControl.evaluate (pairedValues Q P grid v)

theorem finishControl_valid : finishControl.Valid ids := by
  simp [finishControl,Control.prepend,finishInstructions,halveControl,Control.Valid,
    RationalDataflow.Instruction.Valid,ids]
theorem finishControl_admissible (v : ℕ→Parts) : finishControl.AdmissibleTrace v := by
  simp [finishControl,Control.prepend,finishInstructions,halveControl,Control.AdmissibleTrace,
    RationalDataflow.Instruction.Admissible]

#print axioms restart_width
#print axioms restart_input
end Maxwell.Continuum.Profile.WaveMachine.Runtime
