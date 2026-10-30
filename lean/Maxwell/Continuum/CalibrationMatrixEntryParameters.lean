import Maxwell.Continuum.CalibrationMatrixEntryReset

/-! The literal matrix-entry arithmetic preserves the five physical
parameters. This supplies the loop invariant for repeated table generation. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem matrixControl_parameter (v : ℕ→Parts) (k : ℕ) (hk : k∈matrixParameters) :
    RawFree.matrixControl.evaluate v k=v k := by
  have cases : k=0 ∨ k=1 ∨ k=16 ∨ k=17 ∨ k=18 := by
    simpa only [matrixParameters,Finset.mem_insert,Finset.mem_singleton] using hk
  rw [RawFree.matrixControl,Control.prepend_evaluate]
  change RawFree.matrixTail.evaluate (RawFree.matrixGuard v) k=v k
  have keep := RawFree.matrixGuard_keep v k (by omega)
  rw [RawFree.matrixTail,Control.evaluate]
  split_ifs
  · rw [RawFree.matrixYes,Control.andThen_evaluate,Control.andThen_evaluate]
    have finish (w : ℕ→Parts) : RawFree.matrixFinish.evaluate w k=w k := by
      simp (disch := omega) only [RawFree.matrixFinish,Control.evaluate,Instruction.update,
        Function.update_of_ne]
    rw [finish,RawFree.neighborSum_other _ k (by omega),RawFree.indexedFree_other _ k (by omega)]
    exact keep
  · simpa only [Control.evaluate,Instruction.update,Function.update_of_ne (show k≠12 by omega)] using keep

theorem matrixEntry_parameter (v : ℕ→Parts) (n : ℕ→ℕ) (k : ℕ) (hk : k∈matrixParameters) :
    matrixEntryOutput v n k=v k := by
  rw [matrixEntryOutput,matrixControl_parameter _ k hk]
  have cases : k=0 ∨ k=1 ∨ k=16 ∨ k=17 ∨ k=18 := by
    simpa only [matrixParameters,Finset.mem_insert,Finset.mem_singleton] using hk
  exact matrixParts_input n v k (by omega)

#print axioms matrixEntry_parameter

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
