import Maxwell.Continuum.ChebyshevWaveLocalWidths
import Maxwell.Continuum.ChebyshevWaveMachineProductWidths

/-! Fourier-summand words are bounded from their actual operands, independently
of the already accumulated Fourier sum. -/
namespace Maxwell.Continuum.Profile.WaveMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem character_width_local (P W : ℕ) (v : ℕ→Parts) (h5 : (v 5).Width W) :
    (reducedTurn v).Width (3*W+4) ∧ (characterReal P v).Width (characterWidth P W) ∧
      (characterImag P v).Width (characterWidth P W) := by
  have hf := DyadicFloor.result_width 0 W (v 5) h5
  have hr : (reducedTurn v).Width (3*W+4) := by
    have h := Parts.Width.sub h5 hf
    simpa only [reducedTurn,fractionalValue,show W+(2*W+0+3)+1=3*W+4 by omega] using h
  exact ⟨hr,Phase.result_width _ _ _ _ _ hr,Phase.result_width _ _ _ _ _ hr⟩

theorem product_states_width_local (Q P W B : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v)
    (h0 : (v 0).Width W) (h1 : (v 1).Width W) (h5 : (v 5).Width W) :
    WidthBank ids (B+productInputWidth Q P W) (sampleValues Q P v) ∧
    WidthBank ids (B+productInputWidth Q P W) (state4 Q P v) ∧
    WidthBank ids (B+productInputWidth Q P W) (state5 Q P v) ∧
    WidthBank ids (B+productInputWidth Q P W) (state6 Q P v) ∧
    WidthBank ids (B+productInputWidth Q P W) (state7 Q P v) := by
  have hb := (states_width_local Q P W B v hw h0 h1).2.2.2.2.mono
    (show B+workWidth Q P W≤B+productInputWidth Q P W by unfold productInputWidth;omega)
  have hc := character_width_local P W v h5
  have b4 := hb.update 2 ((DyadicFloor.result_width 0 W (v 5) h5).mono
    (show 2*W+0+3≤B+productInputWidth Q P W by unfold productInputWidth;omega))
  have b5 := b4.update 5 (hc.1.mono (show 3*W+4≤B+productInputWidth Q P W by unfold productInputWidth;omega))
  have b6 := b5.update 6 (hc.2.1.mono (show characterWidth P W≤B+productInputWidth Q P W by unfold productInputWidth;omega))
  exact ⟨hb,b4,b5,b6,b6.update 7 (hc.2.2.mono (by unfold productInputWidth;omega))⟩

theorem product_widthTrace_local (Q P W B : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v)
    (h0 : (v 0).Width W) (h1 : (v 1).Width W) (h5 : (v 5).Width W) :
    WidthTrace ids (64*(B+productInputWidth Q P W+1)) productInstructions (state7 Q P v) := by
  have h := (product_states_width_local Q P W B v hw h0 h1 h5).2.2.2.2
  exact inferred_widthTrace ids productInstructions productInstructions_valid (fun _ => B+productInputWidth Q P W)
    (state7 Q P v) h _ (h.mono (by omega)) (product_program_width _)

theorem product_output_width_local (Q P W : ℕ) (v : ℕ→Parts)
    (h0 : (v 0).Width W) (h1 : (v 1).Width W) (h5 : (v 5).Width W) :
    (productValues Q P v 0).Width (productWorkWidth Q P W) ∧
    (productValues Q P v 1).Width (productWorkWidth Q P W) := by
  have hs := values_width_local Q P W v h0 h1
  have hc := character_width_local P W v h5
  have hreal := (hc.2.1.mul hs.2.2.1).sub (hc.2.2.mul hs.2.2.2)
  have himag := (hc.2.1.mul hs.2.2.2).add (hc.2.2.mul hs.2.2.1)
  have hbound : (characterWidth P W+outerWidth Q P W+1)+
      (characterWidth P W+outerWidth Q P W+1)+1≤productWorkWidth Q P W := by
    unfold productWorkWidth productInputWidth workWidth
    omega
  have hprod := productInstructions_values (state7 Q P v)
  have h6 : state7 Q P v 6=characterReal P v := by simp [state7,state6]
  have h7 : state7 Q P v 7=characterImag P v := by simp [state7]
  have h3 : state7 Q P v 3=realValue Q P v := by simp [state7,state6,state5,state4,sampleValues,state3]
  have h4 : state7 Q P v 4=imagValue Q P v := by simp [state7,state6,state5,state4,sampleValues]
  rw [h6,h7,h3,h4] at hprod
  constructor
  · change (evaluate productInstructions (state7 Q P v) 0).Width _
    rw [hprod.1]
    exact hreal.mono hbound
  · change (evaluate productInstructions (state7 Q P v) 1).Width _
    rw [hprod.2]
    exact himag.mono hbound

#print axioms product_output_width_local
#print axioms product_widthTrace_local
end Maxwell.Continuum.Profile.WaveMachine
