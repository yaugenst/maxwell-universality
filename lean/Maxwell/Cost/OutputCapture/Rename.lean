import Maxwell.Cost.OutputCapture.Footprint
import Maxwell.Cost.Structured.Rename

/-! Output-capture non-access transports through a fixed tape renaming. -/
namespace Maxwell.Cost.OutputCapture
open Structured

theorem avoids_rename (archive : ℕ) (p : Equiv.Perm ℕ) (instruction : BitRAMInstruction) :
    avoids archive (instruction.renameTapes p)=avoids (p.symm archive) instruction := by
  cases instruction <;> simp [BitRAMInstruction.renameTapes,avoids,Equiv.apply_eq_iff_eq_symm_apply]

theorem renamed_call_avoids (archive : ℕ) (p : Equiv.Perm ℕ) (body : Code)
    (h : avoidsCode (p.symm archive) body=true) :
    avoidsCode archive (.call (body.compile.renameTapes p))=true := by
  simpa only [avoidsCode,BitRAM.renameTapes,List.all_map,Function.comp_def,
    avoids_rename,compile_avoids] using h

#print axioms renamed_call_avoids
end Maxwell.Cost.OutputCapture
