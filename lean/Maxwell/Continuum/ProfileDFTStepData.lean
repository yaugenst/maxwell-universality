import Maxwell.Continuum.ProfileAngularLoaded
import Maxwell.Continuum.ProfileRawWidths

/-! One literal profile DFT term uses runtime argument and frequency
registers and adds its computed value to the cached accumulator. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000

def dftPreparation : List Instruction := [.binary .mul 6 0 5]
def dftFinish : List Instruction := [.binary .mul 8 4 7,.binary .add 9 9 8]
def dftAfterPreparation (P : ℕ) (v : ℕ→Parts) : ℕ→Parts := evaluate dftPreparation (angularValues P v)
def dftAfterPhase (D P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (dftAfterPreparation P v) 7
    (Phase.result cosineSigns (D+1) P (dftAfterPreparation P v 6))
def dftStepValues (D P : ℕ) (v : ℕ→Parts) : ℕ→Parts := evaluate dftFinish (dftAfterPhase D P v)
def dftStepCode : Code := .seq angularLoadedCode (.seq (program dftPreparation)
  (.seq (Phase.Runtime.loadedCode RationalTaylor.Runtime.cosineCycle 7 6 669 663) (program dftFinish)))
def dftStepCost (D P W : ℕ) : ℕ := 96*(W+1)+angularCost P W+(operationCost W+1)+
  (64*(W+1)+Phase.Runtime.costBound (D+1) P W)+(2*operationCost W+1)
def dftScratchWidth (U : ℕ) : ℕ :=
  angularRawWidth U+angularPhaseWidth U+dftPhaseWidth U+2*(U+1)+10

theorem angularValues_zero (P : ℕ) (v : ℕ→Parts) : angularValues P v 0=v 0 := by
  simp [angularValues,angularAfterMiddle,angularMiddle,evaluate,Instruction.update,angularAfterPhase]
theorem angularValues_large (P : ℕ) (v : ℕ→Parts) (i : ℕ) (hi : 5 ≤ i) : angularValues P v i=v i := by
  simp (disch := omega) [angularValues,angularAfterMiddle,angularMiddle,evaluate,Instruction.update,angularAfterPhase]

theorem dftAfterPreparation_argument (P : ℕ) (v : ℕ→Parts) :
    dftAfterPreparation P v 6=(v 0).mul (v 5) := by
  simp [dftAfterPreparation,dftPreparation,evaluate,Instruction.update,BinaryOp.eval,
    angularValues_zero,angularValues_large]

theorem dftAfterPhase_sample (D P : ℕ) (v : ℕ→Parts) :
    dftAfterPhase D P v 4=angularParts P (v 0) := by
  simp [dftAfterPhase,dftAfterPreparation,dftPreparation,evaluate,Instruction.update,angularValues_output]

theorem dftStepValues_term (D P : ℕ) (v : ℕ→Parts) :
    dftStepValues D P v 8=(angularParts P (v 0)).mul
      (Phase.result cosineSigns (D+1) P ((v 0).mul (v 5))) := by
  simp [dftStepValues,dftFinish,evaluate,Instruction.update,BinaryOp.eval,
    dftAfterPhase,dftAfterPreparation,dftPreparation,angularValues_output,angularValues_zero,angularValues_large]

theorem dftStepValues_accumulator (D P : ℕ) (v : ℕ→Parts) :
    dftStepValues D P v 9=(v 9).add ((angularParts P (v 0)).mul
      (Phase.result cosineSigns (D+1) P ((v 0).mul (v 5)))) := by
  simp [dftStepValues,dftFinish,evaluate,Instruction.update,BinaryOp.eval,
    dftAfterPhase,dftAfterPreparation,dftPreparation,
    angularValues_output,angularValues_zero,angularValues_large]

theorem dftStepValues_actual_term (grid D P j : ℕ) (k : ℤ) (v : ℕ→Parts)
    (hx : v 0=gridArgument grid j) (hk : v 5=integerArgument (-k)) :
    dftStepValues D P v 8=dftTerm grid D P k j ∧
      dftStepValues D P v 9=(v 9).add (dftTerm grid D P k j) := by
  rw [dftStepValues_term,dftStepValues_accumulator,hx,hk]
  exact ⟨rfl,rfl⟩

theorem dftPreparation_valid (S : Finset ℕ) (hS : Finset.range 10⊆S) :
    ∀a∈dftPreparation,a.Valid S := by
  simp [dftPreparation,Instruction.Valid,hS (show 0∈Finset.range 10 by decide),
    hS (show 5∈Finset.range 10 by decide),hS (show 6∈Finset.range 10 by decide)]
theorem dftFinish_valid (S : Finset ℕ) (hS : Finset.range 10⊆S) :
    ∀a∈dftFinish,a.Valid S := by
  simp [dftFinish,Instruction.Valid,hS (show 4∈Finset.range 10 by decide),
    hS (show 7∈Finset.range 10 by decide),hS (show 8∈Finset.range 10 by decide),
    hS (show 9∈Finset.range 10 by decide)]

theorem angularValues_width (S : Finset ℕ) (P U W : ℕ) (v : ℕ→Parts)
    (hw : WidthBank S W v) (hx : (v 0).Width (U+1)) (hP : P≤U)
    (hW : angularRawWidth U+angularPhaseWidth U+2≤W) : WidthBank S W (angularValues P v) := by
  have hp := (Phase.result_width cosineSigns 1 (P+4) (U+1) (v 0) hx).mono
    (show 2^68*(1+(P+4)+(U+1)+12)^4≤angularPhaseWidth U from
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))
  have hcos := hw.update 1 (hp.mono (by omega))
  have hone := hcos.update 2 ((Parts.literal_width RationalWords.width_one).mono (by omega))
  have hsub := hone.update 3 (((Parts.literal_width RationalWords.width_one).sub hp).mono (by omega))
  have hlast := hsub.update 4 ((angularParts_width P U (v 0) hP hx).mono (by omega))
  simpa [angularValues,angularAfterMiddle,angularMiddle,evaluate,Instruction.update,
    BinaryOp.eval,angularAfterPhase] using hlast

theorem dftPreparation_width (S : Finset ℕ) (P U W : ℕ) (v : ℕ→Parts)
    (hw : WidthBank S W (angularValues P v)) (hx : (v 0).Width (U+1))
    (hk : (v 5).Width (U+1)) (hW : 2*(U+1)+1≤W) :
    WidthTrace S W dftPreparation (angularValues P v) := by
  refine ⟨hw,trivial,?_⟩
  have hh := hw.update 6 ((hx.mul hk).mono (by omega))
  simpa [Instruction.update,BinaryOp.eval,angularValues_zero,angularValues_large,WidthTrace] using hh

theorem dftAfterPhase_width (S : Finset ℕ) (D P U W : ℕ) (v : ℕ→Parts)
    (hw : WidthBank S W (dftAfterPreparation P v))
    (hx : (v 0).Width (U+1)) (hk : (v 5).Width (U+1))
    (hD : D≤U) (hP : P≤U) (hW : dftPhaseWidth U≤W) :
    WidthBank S W (dftAfterPhase D P v) := by
  apply hw.update 7
  rw [dftAfterPreparation_argument]
  have hi := (hx.mul hk).mono (show (U+1)+(U+1)+1≤2*(U+1)+1 by omega)
  exact (Phase.result_width cosineSigns (D+1) P _ _ hi).mono
    ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)).trans hW)

theorem dftFinish_width (S : Finset ℕ) (D P U B W : ℕ) (v : ℕ→Parts)
    (hw : WidthBank S W (dftAfterPhase D P v))
    (hx : (v 0).Width (U+1)) (hk : (v 5).Width (U+1)) (hacc : (v 9).Width B)
    (hD : D≤U) (hP : P≤U) (hW : B+dftTermWidth U+1≤W) :
    WidthTrace S W dftFinish (dftAfterPhase D P v) := by
  have ha := angularParts_width P U (v 0) hP hx
  have hi := (hx.mul hk).mono (show (U+1)+(U+1)+1≤2*(U+1)+1 by omega)
  have hp := (Phase.result_width cosineSigns (D+1) P _ _ hi).mono
    (show 2^68*((D+1)+P+(2*(U+1)+1)+12)^4≤dftPhaseWidth U from
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))
  have ht : ((angularParts P (v 0)).mul (Phase.result cosineSigns (D+1) P ((v 0).mul (v 5)))).Width
      (dftTermWidth U) := ha.mul hp
  have hterm := hw.update 8 (ht.mono (by omega))
  refine ⟨hw,trivial,?_,trivial,?_⟩
  · simpa [Instruction.update,BinaryOp.eval,dftAfterPhase,
      dftAfterPreparation,dftPreparation,evaluate,angularValues_output,angularValues_zero,angularValues_large] using hterm
  · have hh := hterm.update 9 ((hacc.add ht).mono hW)
    simpa [Instruction.update,BinaryOp.eval,WidthTrace,dftAfterPhase,
      dftAfterPreparation,dftPreparation,evaluate,angularValues_output,angularValues_zero,angularValues_large] using hh

#print axioms dftStepValues_actual_term
#print axioms dftFinish_width
end Maxwell.Continuum.Profile.Runtime
