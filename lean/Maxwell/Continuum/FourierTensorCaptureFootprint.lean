import Maxwell.Continuum.FourierTensorModeCompleteComponent
import Maxwell.Continuum.OutputCaptureLiteral

/-! The fixed component compiler never accesses the retained template
payload tape. Literal rational bits do not need to be evaluated. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536

private theorem avoids_seq (archive : ℕ) (a b : Code)
    (ha : OutputCapture.avoidsCode archive a=true) (hb : OutputCapture.avoidsCode archive b=true) :
    OutputCapture.avoidsCode archive (.seq a b)=true := by
  simp only [OutputCapture.avoidsCode,ha,hb,Bool.and_self]

theorem completeComponent_avoids992 (j : Fin 3) :
    OutputCapture.avoidsCode 992 (completeComponentCode j)=true := by
  fin_cases j <;>
    repeat' first
    | decide
    | exact OutputCapture.literal_write_avoids _ _ _ (by decide)
    | exact OutputCapture.literal_avoids _ _ _ (by decide)
    | apply avoids_seq

#print axioms completeComponent_avoids992
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
