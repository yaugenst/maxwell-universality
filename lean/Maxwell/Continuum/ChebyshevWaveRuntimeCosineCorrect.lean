import Maxwell.Continuum.ChebyshevWaveRuntimeCosineData
import Maxwell.Continuum.ChebyshevWaveRounded

/-! The two actual raw Fourier passes and their runtime zero-index correction
compute the exact rational cosine coefficient used by the finite encoder. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem pairedValues_good (Q P grid : ℕ) (v : ℕ→Parts) (hv : Good ids v) :
    Good ids (pairedValues Q P grid v) := by
  have hp := coefficientValues_good Q P grid v hv
  exact ((coefficientValues_good Q P grid _ (restart_good _ hp)).update 2 (hp 8 (by decide))).update
    3 (hp 9 (by decide))

theorem finish_values (j : ℕ) (v : ℕ→Parts) (hv : Good ids v) (hn : (v 12).value=-(j:ℚ)) :
    ((finishControl.evaluate v) 8).value=
      (if j=0 then ((v 2).value+(v 8).value)/2 else (v 2).value+(v 8).value) ∧
    ((finishControl.evaluate v) 9).value=
      (if j=0 then ((v 3).value+(v 9).value)/2 else (v 3).value+(v 9).value) := by
  have h := finishControl.evaluate_value ids finishControl_valid v hv (finishControl_admissible v)
  have h8 := congrFun h 8
  have h9 := congrFun h 9
  by_cases hj : j=0
  · subst j
    constructor
    · simpa [finishControl,Control.prepend,finishInstructions,Control.rationalEvaluate,
        RationalDataflow.Instruction.rationalUpdate,halveControl,valueBank,Function.update_apply,
        hn,div_eq_mul_inv,mul_comm] using h8
    · simpa [finishControl,Control.prepend,finishInstructions,Control.rationalEvaluate,
        RationalDataflow.Instruction.rationalUpdate,halveControl,valueBank,Function.update_apply,
        hn,div_eq_mul_inv,mul_comm] using h9
  · have hjp : 0<(j:ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hj
    simp [finishControl,Control.prepend,finishInstructions,Control.rationalEvaluate,
      RationalDataflow.Instruction.rationalUpdate,halveControl,valueBank,
      hn,hjp,hj] at h8 h9 ⊢
    exact ⟨h8,h9⟩

theorem cosineValues_correct (grid : ℕ) [NeZero grid] (q : ℚ) (j Q P : ℕ) (v : ℕ→Parts)
    (hv : Good ids v) (hi : SumInput grid q (j:ℤ) 0 v)
    (hz0 : (v 8).value=0) (hz1 : (v 9).value=0) :
    (cosineValues Q P grid v 8).value=(rationalWaveCosineCoefficient grid q Q P j).re.center ∧
    (cosineValues Q P grid v 9).value=(rationalWaveCosineCoefficient grid q Q P j).im.center := by
  have hp := coefficientValues_correct grid q (j:ℤ) Q P v hv hi hz0 hz1
  have hv1 := coefficientValues_good Q P grid v hv
  have hi1 := restart_input Q P grid q (j:ℤ) v hi
  have hm := coefficientValues_correct grid q (-(j:ℤ)) Q P _ (restart_good _ hv1) hi1
    (restart_zero _ 8 (by decide)) (restart_zero _ 9 (by decide))
  have hn : (pairedValues Q P grid v 12).value=-(j:ℚ) := by
    simp only [pairedValues,Function.update_of_ne (by decide : (12:ℕ)≠3),
      Function.update_of_ne (by decide : (12:ℕ)≠2),secondValues,
      coefficientValues_unchanged_high Q P grid _ 12 (by decide) (by decide)]
    simpa only [Int.cast_neg,Int.cast_natCast] using hi1.index
  have hf := finish_values j _ (pairedValues_good Q P grid v hv) hn
  change (finishControl.evaluate (pairedValues Q P grid v) 8).value=_ ∧
    (finishControl.evaluate (pairedValues Q P grid v) 9).value=_
  rw [hf.1,hf.2]
  simp only [pairedValues,Function.update_self,
    Function.update_of_ne (by decide : (2:ℕ)≠3),Function.update_of_ne (by decide : (8:ℕ)≠3),
    Function.update_of_ne (by decide : (8:ℕ)≠2),Function.update_of_ne (by decide : (9:ℕ)≠3),
    Function.update_of_ne (by decide : (9:ℕ)≠2),secondValues,hp.1,hp.2,hm.1,hm.2]
  by_cases hj : j=0
  · subst j
    simp [rationalWaveCosineCoefficient]
  · simp [rationalWaveCosineCoefficient,hj,Maxwell.Certificate.ComplexRectangle.add,
      Maxwell.Certificate.Ball.add]

theorem cosineValues_good (Q P grid : ℕ) (v : ℕ→Parts) (hv : Good ids v) :
    Good ids (cosineValues Q P grid v) :=
  finishControl.evaluate_good ids finishControl_valid _ (pairedValues_good Q P grid v hv)
    (finishControl_admissible _)

theorem cosineValues_center (grid : ℕ) [NeZero grid] (q : ℚ) (j Q P : ℕ) (v : ℕ→Parts)
    (hv : Good ids v) (hi : SumInput grid q (j:ℤ) 0 v)
    (hz0 : (v 8).value=0) (hz1 : (v 9).value=0) :
    storedCenter (cosineValues Q P grid v)=
      Calibration.rectangleCenter (rationalWaveCosineCoefficient grid q Q P j) := by
  have h := cosineValues_correct grid q j Q P v hv hi hz0 hz1
  simp only [storedCenter,Calibration.rectangleCenter,h.1,h.2]

theorem cosineValues_error (grid D K P : ℕ) [NeZero grid] (q : ℚ) (Q j : ℕ)
    (hq : |q| ≤ Q) (hk : |2*Real.pi*(q:ℝ)| ≤ K) (hj : j ≤ D)
    (hgrid : waveDegree K P+D ≤ grid) (v : ℕ→Parts) (hv : Good ids v)
    (hi : SumInput grid q (j:ℤ) 0 v) (hz0 : (v 8).value=0) (hz1 : (v 9).value=0) :
    ‖waveCosineCoefficient (2*Real.pi*(q:ℝ)) j-storedCenter (cosineValues Q P grid v)‖ ≤
      18*(1/2:ℝ)^P := by
  rw [cosineValues_center grid q j Q P v hv hi hz0 hz1]
  exact rationalWaveCosineCoefficient_error grid D K P q Q j hq hk hj hgrid

#print axioms cosineValues_correct
#print axioms cosineValues_error
end Maxwell.Continuum.Profile.WaveMachine.Runtime
