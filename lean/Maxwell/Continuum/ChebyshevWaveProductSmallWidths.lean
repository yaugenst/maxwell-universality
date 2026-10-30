import Maxwell.Continuum.ChebyshevWaveProductLocalWidths
import Maxwell.Continuum.RationalDataflowTraceResult

/-! Every overwritten sample register has a bound independent of the sums. -/
namespace Maxwell.Continuum.Profile.WaveMachine
open RationalDataflow RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem state7_small_width (Q P W : ℕ) (v : ℕ→Parts)
    (h0 : (v 0).Width W) (h1 : (v 1).Width W) (h5 : (v 5).Width W) :
    WidthBank (Finset.range 8) (productInputWidth Q P W) (state7 Q P v) := by
  have hs := values_width_local Q P W v h0 h1
  have hc := character_width_local P W v h5
  have hf := DyadicFloor.result_width 0 W (v 5) h5
  have hw : W≤productInputWidth Q P W := by unfold productInputWidth workWidth;omega
  have hfloor : 2*W+0+3≤productInputWidth Q P W := by unfold productInputWidth;omega
  have hred : 3*W+4≤productInputWidth Q P W := by unfold productInputWidth;omega
  have houter : outerWidth Q P W≤productInputWidth Q P W := by unfold productInputWidth workWidth;omega
  have hchar : characterWidth P W≤productInputWidth Q P W := by unfold productInputWidth;omega
  intro i hi
  have hi' := Finset.mem_range.mp hi
  interval_cases i <;>
    simp only [state7,state6,state5,state4,sampleValues,state3,state2,state1,
      Function.update_apply] <;> norm_num
  · exact h0.mono hw
  · exact h1.mono hw
  · exact hf.mono hfloor
  · exact hs.2.2.1.mono houter
  · exact hs.2.2.2.mono houter
  · exact hc.1.mono hred
  · exact hc.2.1.mono hchar
  · exact hc.2.2.mono hchar

theorem product_small_width (Q P W : ℕ) (v : ℕ→Parts)
    (h0 : (v 0).Width W) (h1 : (v 1).Width W) (h5 : (v 5).Width W) :
    WidthBank (Finset.range 8) (productWorkWidth Q P W) (productValues Q P v) := by
  have hvalid : ∀a∈productInstructions,a.Valid (Finset.range 8) := by
    simp [productInstructions,RationalDataflow.Instruction.Valid]
  have h := state7_small_width Q P W v h0 h1 h5
  exact (inferred_widthTrace (Finset.range 8) productInstructions hvalid
    (fun _ => productInputWidth Q P W) (state7 Q P v) h (productWorkWidth Q P W)
      (h.mono (by unfold productWorkWidth;omega)) (product_program_width _)).result

#print axioms product_small_width
end Maxwell.Continuum.Profile.WaveMachine
