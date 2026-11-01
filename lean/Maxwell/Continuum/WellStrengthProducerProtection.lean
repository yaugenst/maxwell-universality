import Maxwell.Continuum.WellStrengthTableProduction
import Maxwell.Cost.Structured.TapeInterval

/-! Serializer inputs survive the complete strength producer. These finite
syntax checks cover the existing executed program, including every loop. -/
namespace Maxwell.Continuum.RationalDataflow.WellStrengthPass
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

theorem code_preserves_payload : code.outsideTapes 990 993=true:=by decide +kernel
theorem code_preserves_input_headers : code.outsideTapes 200 206=true:=by decide +kernel
theorem code_preserves_serializer_cursors : code.outsideTapes 727 729=true:=by decide +kernel

#print axioms code_preserves_payload
#print axioms code_preserves_input_headers
#print axioms code_preserves_serializer_cursors
end Maxwell.Continuum.RationalDataflow.WellStrengthPass
