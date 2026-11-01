import Maxwell.Continuum.FourierTensorCaptureFootprint
import Maxwell.Cost.Structured.Footprint

/-! The computed component preserves the retained site count and profile
payload, including their heads and all occupied cells. -/

namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536

private theorem avoids_seq (archive : ℕ) (a b : Code)
    (ha : OutputCapture.avoidsCode archive a=true) (hb : OutputCapture.avoidsCode archive b=true) :
    OutputCapture.avoidsCode archive (.seq a b)=true := by
  simp only [OutputCapture.avoidsCode,ha,hb,Bool.and_self]

theorem completeComponent_avoids988 (j : Fin 3) :
    OutputCapture.avoidsCode 988 (completeComponentCode j)=true := by
  fin_cases j <;>
    repeat' first
    | decide
    | exact OutputCapture.literal_write_avoids _ _ _ (by decide)
    | exact OutputCapture.literal_avoids _ _ _ (by decide)
    | apply avoids_seq

theorem completeComponent_avoids991 (j : Fin 3) :
    OutputCapture.avoidsCode 991 (completeComponentCode j)=true := by
  fin_cases j <;>
    repeat' first
    | decide
    | exact OutputCapture.literal_write_avoids _ _ _ (by decide)
    | exact OutputCapture.literal_avoids _ _ _ (by decide)
    | apply avoids_seq

theorem completeComponent_protects988 (j : Fin 3) :
    (completeComponentCode j).protectsTape 988=true :=
  OutputCapture.avoidsCode_protectsTape _ _ (completeComponent_avoids988 j)

theorem completeComponent_protects991 (j : Fin 3) :
    (completeComponentCode j).protectsTape 991=true :=
  OutputCapture.avoidsCode_protectsTape _ _ (completeComponent_avoids991 j)

theorem completeComponent_retained {j : Fin 3} {input : List Bool} {randomTape : ℕ→Bool}
    {cost : ℕ} {s t : Store} (run : Executes input randomTape (completeComponentCode j) cost s t) :
    t.val.tapes 988=s.val.tapes 988 ∧ t.val.tapes 991=s.val.tapes 991 :=
  ⟨run.protectsTape _ (completeComponent_protects988 j),
    run.protectsTape _ (completeComponent_protects991 j)⟩

#print axioms completeComponent_retained
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
