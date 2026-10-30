import Maxwell.Continuum.ChebyshevWaveMachineData

/-! Sample output widths depend only on the two actual sample operands.
The independently growing Fourier accumulator is only charged as stored data. -/
namespace Maxwell.Continuum.Profile.WaveMachine
open RationalDataflow RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem values_width_local (Q P W : ℕ) (v : ℕ→Parts)
    (h0 : (v 0).Width W) (h1 : (v 1).Width W) :
    (innerValue Q P v).Width (innerWidth Q P W) ∧
    (argumentValue Q P v).Width (argumentWidth Q P W) ∧
    (realValue Q P v).Width (outerWidth Q P W) ∧
    (imagValue Q P v).Width (outerWidth Q P W) := by
  have hi := Phase.result_width cosineSigns 1 (Calibration.phaseBits Q (P+4)) W (v 1) h1
  have ha := Parts.Width.mul h0 hi
  exact ⟨hi,ha,Phase.result_width _ _ _ _ _ ha,Phase.result_width _ _ _ _ _ ha⟩

theorem states_width_local (Q P W B : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v)
    (h0 : (v 0).Width W) (h1 : (v 1).Width W) :
    WidthBank ids (B+workWidth Q P W) v ∧
    WidthBank ids (B+workWidth Q P W) (state1 Q P v) ∧
    WidthBank ids (B+workWidth Q P W) (state2 Q P v) ∧
    WidthBank ids (B+workWidth Q P W) (state3 Q P v) ∧
    WidthBank ids (B+workWidth Q P W) (sampleValues Q P v) := by
  have hb := hw.mono (Nat.le_add_right B (workWidth Q P W))
  have hv := values_width_local Q P W v h0 h1
  have b1 := hb.update 2 (hv.1.mono (show innerWidth Q P W≤B+workWidth Q P W by unfold workWidth;omega))
  have b2 := b1.update 2 (hv.2.1.mono (show argumentWidth Q P W≤B+workWidth Q P W by unfold workWidth;omega))
  have b3 := b2.update 3 (hv.2.2.1.mono (show outerWidth Q P W≤B+workWidth Q P W by unfold workWidth;omega))
  exact ⟨hb,b1,b2,b3,b3.update 4 (hv.2.2.2.mono
    (show outerWidth Q P W≤B+workWidth Q P W by unfold workWidth;omega))⟩

#print axioms states_width_local
end Maxwell.Continuum.Profile.WaveMachine
