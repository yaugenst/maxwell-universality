import Maxwell.Continuum.ChebyshevWaveMachineProductData

/-! All intermediate raw-width conditions for the finite Fourier
summand are derived from the stored inputs. -/
namespace Maxwell.Continuum.Profile.WaveMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def characterWidth (P W : ℕ) : ℕ := 2^68*(1+P+(3*W+4)+12)^4
def productInputWidth (Q P W : ℕ) : ℕ :=
  workWidth Q P W+(2*W+3)+(3*W+4)+characterWidth P W+1
def productWorkWidth (Q P W : ℕ) : ℕ := 64*(productInputWidth Q P W+1)

theorem character_width (P W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v) :
    (reducedTurn v).Width (3*W+4) ∧ (characterReal P v).Width (characterWidth P W) ∧
      (characterImag P v).Width (characterWidth P W) := by
  have hf := DyadicFloor.result_width 0 W (v 5) (hw 5 (by decide))
  have hr : (reducedTurn v).Width (3*W+4) := by
    have h := Parts.Width.sub (hw 5 (by decide)) hf
    simpa only [reducedTurn,fractionalValue,
      show W+(2*W+0+3)+1=3*W+4 by omega] using h
  exact ⟨hr,Phase.result_width _ _ _ _ _ hr,Phase.result_width _ _ _ _ _ hr⟩

theorem product_states_width (Q P W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v) :
    WidthBank ids (productInputWidth Q P W) (sampleValues Q P v) ∧
    WidthBank ids (productInputWidth Q P W) (state4 Q P v) ∧
    WidthBank ids (productInputWidth Q P W) (state5 Q P v) ∧
    WidthBank ids (productInputWidth Q P W) (state6 Q P v) ∧
    WidthBank ids (productInputWidth Q P W) (state7 Q P v) := by
  have h0 := (states_width Q P W v hw).2.2.2.2.mono
    (show workWidth Q P W≤productInputWidth Q P W by unfold productInputWidth;omega)
  have hc := character_width P W v hw
  have h4 := h0.update 2 ((DyadicFloor.result_width 0 W (v 5) (hw 5 (by decide))).mono
    (show 2*W+0+3≤productInputWidth Q P W by unfold productInputWidth;omega))
  have h5 := h4.update 5 (hc.1.mono (show 3*W+4≤productInputWidth Q P W by unfold productInputWidth;omega))
  have h6 := h5.update 6 (hc.2.1.mono (show characterWidth P W≤productInputWidth Q P W by unfold productInputWidth;omega))
  exact ⟨h0,h4,h5,h6,h6.update 7 (hc.2.2.mono (by unfold productInputWidth;omega))⟩

theorem product_program_width (B : ℕ) : programWidth productInstructions (fun _ => B)≤64*(B+1) := by
  simp [productInstructions,programWidth,RationalDataflow.Instruction.widthUpdate,
    RationalDataflow.Instruction.resultWidth]
  omega

theorem product_widthTrace (Q P W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v) :
    WidthTrace ids (productWorkWidth Q P W) productInstructions (state7 Q P v) := by
  have h := (product_states_width Q P W v hw).2.2.2.2
  exact inferred_widthTrace ids productInstructions productInstructions_valid (fun _ => productInputWidth Q P W)
    (state7 Q P v) h (productWorkWidth Q P W) (h.mono (by unfold productWorkWidth;omega))
      (product_program_width _)

theorem product_states_good (Q P : ℕ) (v : ℕ→Parts) (hv : Good ids v) :
    Good ids (state4 Q P v) ∧ Good ids (state5 Q P v) ∧ Good ids (state6 Q P v) ∧
      Good ids (state7 Q P v) ∧ Good ids (productValues Q P v) := by
  have h0 := (states_good Q P v hv).2.2.2
  have hc := character_valid P v hv
  have h4 := h0.update 2 (DyadicFloor.result_valid 0 (v 5))
  have h5 := h4.update 5 hc.1
  have h6 := h5.update 6 hc.2.1
  have h7 := h6.update 7 hc.2.2
  refine ⟨h4,h5,h6,h7,evaluate_good ids productInstructions productInstructions_valid _ h7 ?_⟩
  simp [productInstructions,AdmissibleTrace,RationalDataflow.Instruction.Admissible]

#print axioms product_widthTrace
#print axioms product_states_good
end Maxwell.Continuum.Profile.WaveMachine
