import Maxwell.Continuum.PhaseDataflowFrame
import Maxwell.Continuum.RationalDataflowTrace
import Maxwell.Continuum.ChebyshevWaveEvaluation

/-! Literal register values for the nested cosine used by the finite
Chebyshev wave transform. The input frequency and grid turn remain runtime data. -/
namespace Maxwell.Continuum.Profile.WaveMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def ids : Finset ℕ := Finset.range 16
def innerValue (Q P : ℕ) (v : ℕ→Parts) : Parts :=
  Phase.result cosineSigns 1 (Calibration.phaseBits Q (P+4)) (v 1)
def argumentValue (Q P : ℕ) (v : ℕ→Parts) : Parts := (v 0).mul (innerValue Q P v)
def realValue (Q P : ℕ) (v : ℕ→Parts) : Parts :=
  Phase.result cosineSigns (2*(Q+1)) (P+4) (argumentValue Q P v)
def imagValue (Q P : ℕ) (v : ℕ→Parts) : Parts :=
  Phase.result sineSigns (2*(Q+1)) (P+4) (argumentValue Q P v)
def state1 (Q P : ℕ) (v : ℕ→Parts) : ℕ→Parts := Function.update v 2 (innerValue Q P v)
def state2 (Q P : ℕ) (v : ℕ→Parts) : ℕ→Parts := Function.update (state1 Q P v) 2 (argumentValue Q P v)
def state3 (Q P : ℕ) (v : ℕ→Parts) : ℕ→Parts := Function.update (state2 Q P v) 3 (realValue Q P v)
def sampleValues (Q P : ℕ) (v : ℕ→Parts) : ℕ→Parts := Function.update (state3 Q P v) 4 (imagValue Q P v)

def innerWidth (Q P W : ℕ) : ℕ := 2^68*(1+Calibration.phaseBits Q (P+4)+W+12)^4
def argumentWidth (Q P W : ℕ) : ℕ := W+innerWidth Q P W+1
def outerWidth (Q P W : ℕ) : ℕ := 2^68*(2*(Q+1)+(P+4)+argumentWidth Q P W+12)^4
def workWidth (Q P W : ℕ) : ℕ := W+innerWidth Q P W+argumentWidth Q P W+outerWidth Q P W+1

theorem value_valid (Q P : ℕ) (v : ℕ→Parts) (hv : Good ids v) :
    (innerValue Q P v).Valid ∧ (argumentValue Q P v).Valid ∧
      (realValue Q P v).Valid ∧ (imagValue Q P v).Valid := by
  have hi := Phase.result_valid cosineSigns 1 (Calibration.phaseBits Q (P+4)) (v 1) (hv 1 (by decide))
  have ha := Parts.mul_valid (hv 0 (by decide)) hi
  exact ⟨hi,ha,Phase.result_valid _ _ _ _ ha,Phase.result_valid _ _ _ _ ha⟩

theorem argument_value (Q P : ℕ) (v : ℕ→Parts) (hv : Good ids v) :
    (argumentValue Q P v).value=waveArgument (v 0).value Q P (v 1).value := by
  rw [argumentValue,Parts.mul_value]
  unfold innerValue waveArgument
  rw [Phase.result_cos _ _ _ (hv 1 (by decide))]

theorem sampleValues_correct (Q P : ℕ) (v : ℕ→Parts) (hv : Good ids v) :
    (sampleValues Q P v 3).value=(waveSample (v 0).value Q P (v 1).value).re.center ∧
    (sampleValues Q P v 4).value=(waveSample (v 0).value Q P (v 1).value).im.center := by
  have ha := (value_valid Q P v hv).2.1
  have hc := Phase.result_cos (2*(Q+1)) (P+4) (argumentValue Q P v) ha
  have hs := Phase.result_sin (2*(Q+1)) (P+4) (argumentValue Q P v) ha
  rw [argument_value Q P v hv] at hc hs
  simpa [sampleValues,state3,realValue,imagValue,waveSample] using And.intro hc hs

theorem values_width (Q P W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v) :
    (innerValue Q P v).Width (innerWidth Q P W) ∧
    (argumentValue Q P v).Width (argumentWidth Q P W) ∧
    (realValue Q P v).Width (outerWidth Q P W) ∧
    (imagValue Q P v).Width (outerWidth Q P W) := by
  have hi := Phase.result_width cosineSigns 1 (Calibration.phaseBits Q (P+4)) W (v 1) (hw 1 (by decide))
  have ha := Parts.Width.mul (hw 0 (by decide)) hi
  exact ⟨hi,ha,Phase.result_width _ _ _ _ _ ha,Phase.result_width _ _ _ _ _ ha⟩

theorem states_width (Q P W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v) :
    WidthBank ids (workWidth Q P W) v ∧ WidthBank ids (workWidth Q P W) (state1 Q P v) ∧
    WidthBank ids (workWidth Q P W) (state2 Q P v) ∧ WidthBank ids (workWidth Q P W) (state3 Q P v) ∧
    WidthBank ids (workWidth Q P W) (sampleValues Q P v) := by
  have h0 := hw.mono (show W≤workWidth Q P W by unfold workWidth;omega)
  have hv := values_width Q P W v hw
  have h1 := h0.update 2 (hv.1.mono (show innerWidth Q P W≤workWidth Q P W by unfold workWidth;omega))
  have h2 := h1.update 2 (hv.2.1.mono (show argumentWidth Q P W≤workWidth Q P W by unfold workWidth;omega))
  have h3 := h2.update 3 (hv.2.2.1.mono (show outerWidth Q P W≤workWidth Q P W by unfold workWidth;omega))
  have h4 := h3.update 4 (hv.2.2.2.mono (show outerWidth Q P W≤workWidth Q P W by unfold workWidth;omega))
  exact ⟨h0,h1,h2,h3,h4⟩

theorem states_good (Q P : ℕ) (v : ℕ→Parts) (hv : Good ids v) :
    Good ids (state1 Q P v) ∧ Good ids (state2 Q P v) ∧ Good ids (state3 Q P v) ∧
      Good ids (sampleValues Q P v) := by
  have h := value_valid Q P v hv
  have h1 := hv.update 2 h.1
  have h2 := h1.update 2 h.2.1
  have h3 := h2.update 3 h.2.2.1
  exact ⟨h1,h2,h3,h3.update 4 h.2.2.2⟩

#print axioms sampleValues_correct
#print axioms states_width
end Maxwell.Continuum.Profile.WaveMachine
