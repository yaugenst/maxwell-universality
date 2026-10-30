import Maxwell.Continuum.ChebyshevWaveMachinePhase
import Maxwell.Continuum.DyadicFloorWidths
import Maxwell.Continuum.RationalDataflowRegisterWidths
import Maxwell.Continuum.ChebyshevWaveDFT

/-! Actual reduced Fourier character and complex product registers for
one summand of the plane-wave coefficient. -/
namespace Maxwell.Continuum.Profile.WaveMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def reducedTurn (v : ℕ→Parts) : Parts := fractionalValue (v 5)
def characterReal (P : ℕ) (v : ℕ→Parts) : Parts := Phase.result cosineSigns 1 P (reducedTurn v)
def characterImag (P : ℕ) (v : ℕ→Parts) : Parts := Phase.result sineSigns 1 P (reducedTurn v)
def state4 (Q P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (sampleValues Q P v) 2 (DyadicFloor.result 0 (v 5))
def state5 (Q P : ℕ) (v : ℕ→Parts) : ℕ→Parts := Function.update (state4 Q P v) 5 (reducedTurn v)
def state6 (Q P : ℕ) (v : ℕ→Parts) : ℕ→Parts := Function.update (state5 Q P v) 6 (characterReal P v)
def state7 (Q P : ℕ) (v : ℕ→Parts) : ℕ→Parts := Function.update (state6 Q P v) 7 (characterImag P v)

def productInstructions : List RationalDataflow.Instruction :=
  [.binary .mul 0 6 3,.binary .mul 1 7 4,.binary .sub 0 0 1,
   .binary .mul 1 6 4,.binary .mul 2 7 3,.binary .add 1 1 2]
def productValues (Q P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  evaluate productInstructions (state7 Q P v)

theorem character_valid (P : ℕ) (v : ℕ→Parts) (hv : Good ids v) :
    (reducedTurn v).Valid ∧ (characterReal P v).Valid ∧ (characterImag P v).Valid := by
  have hf := Parts.sub_valid (hv 5 (by decide)) (DyadicFloor.result_valid 0 (v 5))
  exact ⟨hf,Phase.result_valid _ _ _ _ hf,Phase.result_valid _ _ _ _ hf⟩

theorem character_correct (grid : ℕ) [NeZero grid] (P : ℕ) (j : ZMod grid) (n : ℤ)
    (v : ℕ→Parts) (hv : Good ids v) (hturn : (v 5).value= -(j.val:ℚ)*(n:ℚ)/grid) :
    (characterReal P v).value=(Calibration.gridCharacterApprox grid P (-(j*(n:ZMod grid)))).re.center ∧
    (characterImag P v).value=(Calibration.gridCharacterApprox grid P (-(j*(n:ZMod grid)))).im.center := by
  have hf := (character_valid P v hv).1
  have he := fractionalValue_gridTurn grid j n (v 5) (hv 5 (by decide)) hturn
  change (reducedTurn v).value=_ at he
  unfold characterReal characterImag
  rw [Phase.result_cos _ _ _ hf,Phase.result_sin _ _ _ hf,he]
  exact ⟨rfl,rfl⟩

theorem productInstructions_valid : ∀a∈productInstructions,a.Valid ids := by
  simp [productInstructions,RationalDataflow.Instruction.Valid,ids]

theorem productInstructions_values (v : ℕ→Parts) :
    evaluate productInstructions v 0=((v 6).mul (v 3)).sub ((v 7).mul (v 4)) ∧
    evaluate productInstructions v 1=((v 6).mul (v 4)).add ((v 7).mul (v 3)) := by
  simp [productInstructions,evaluate,RationalDataflow.Instruction.update,BinaryOp.eval]

theorem productValues_correct (grid : ℕ) [NeZero grid] (Q P : ℕ) (j : ZMod grid) (n : ℤ)
    (v : ℕ→Parts) (hv : Good ids v)
    (hs : (v 1).value=Calibration.gridTurn grid j)
    (hturn : (v 5).value= -(j.val:ℚ)*(n:ℚ)/grid) :
    (productValues Q P v 0).value=(waveProductSample grid (v 0).value Q P n j).re.center ∧
    (productValues Q P v 1).value=(waveProductSample grid (v 0).value Q P n j).im.center := by
  have hvv := value_valid Q P v hv
  have hcv := character_valid P v hv
  have hc := character_correct grid P j n v hv hturn
  have hsample := sampleValues_correct Q P v hv
  have hp := productInstructions_values (state7 Q P v)
  have h6 : state7 Q P v 6 = characterReal P v := by simp [state7,state6]
  have h7 : state7 Q P v 7 = characterImag P v := by simp [state7]
  have h3 : state7 Q P v 3 = realValue Q P v := by
    simp [state7,state6,state5,state4,sampleValues,state3]
  have h4 : state7 Q P v 4 = imagValue Q P v := by
    simp [state7,state6,state5,state4,sampleValues]
  rw [h6,h7,h3,h4] at hp
  change (realValue Q P v).value=_ ∧ (imagValue Q P v).value=_ at hsample
  constructor
  · change (evaluate productInstructions (state7 Q P v) 0).value=_
    rw [hp.1,Parts.sub_value _ _ (Parts.mul_valid hcv.2.1 hvv.2.2.1)
      (Parts.mul_valid hcv.2.2 hvv.2.2.2),Parts.mul_value,Parts.mul_value,hc.1,hc.2,
      hsample.1,hsample.2,hs]
    simp only [waveProductSample,Maxwell.Certificate.ComplexRectangle.mul,
      Maxwell.Certificate.Ball.mul,Maxwell.Certificate.Ball.add,Maxwell.Certificate.Ball.neg]
    ring
  · change (evaluate productInstructions (state7 Q P v) 1).value=_
    rw [hp.2,Parts.add_value _ _ (Parts.mul_valid hcv.2.1 hvv.2.2.2)
      (Parts.mul_valid hcv.2.2 hvv.2.2.1),Parts.mul_value,Parts.mul_value,hc.1,hc.2,
      hsample.1,hsample.2,hs]
    rfl

#print axioms character_correct
#print axioms productValues_correct
end Maxwell.Continuum.Profile.WaveMachine
