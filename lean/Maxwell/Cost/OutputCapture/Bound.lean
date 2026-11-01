import Maxwell.Cost.OutputCapture.Footprint
import Maxwell.Cost.Structured.TapeBound

/-! Complete tape access bounds discharge output-capture non-access
without expanding literal values or compiled arithmetic circuits. -/
namespace Maxwell.Cost.OutputCapture
open Structured

theorem avoids_of_bound (archive : ℕ) (instruction : BitRAMInstruction)
    (h : instruction.tapeBound≤archive) : avoids archive instruction=true := by
  cases instruction <;> simp_all [avoids,BitRAMInstruction.tapeBound]
  all_goals omega

theorem program_avoids_of_bound (archive : ℕ) (body : BitRAM) (h : body.tapeBound≤archive) :
    body.code.all (avoids archive)=true := by
  apply List.all_eq_true.mpr
  intro instruction member
  exact avoids_of_bound _ _ ((body.tapeBound_le _).mp h instruction member)

theorem code_avoids_of_bound (archive : ℕ) (body : Code) (h : body.tapeBound≤archive) :
    avoidsCode archive body=true := by
  rw [←compile_avoids]
  apply program_avoids_of_bound
  rwa [Code.compile_tapeBound]

#print axioms code_avoids_of_bound
end Maxwell.Cost.OutputCapture
