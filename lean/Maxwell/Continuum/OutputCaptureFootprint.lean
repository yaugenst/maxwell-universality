import Maxwell.Continuum.OutputCaptureCode

/-! Syntactic non-access, including reads, of the retained output tape. -/
namespace Maxwell.Continuum.OutputCapture
open Maxwell.Cost Maxwell.Cost.Structured

def avoidsCode (archive : ℕ) : Code → Bool
  | .skip => true
  | .call body => body.code.all (avoids archive)
  | .seq a b | .branch _ a b => avoidsCode archive a && avoidsCode archive b
  | .loop _ a => avoidsCode archive a

theorem avoids_relocate (archive base exitPC : ℕ) (i : BitRAMInstruction) :
    avoids archive (i.relocate base exitPC)=avoids archive i := by
  cases i <;> rfl

theorem compileAt_avoids (archive : ℕ) (body : Code) (base exitPC : ℕ) :
    (body.compileAt base exitPC).all (avoids archive)=avoidsCode archive body := by
  induction body generalizing base exitPC with
  | skip => rfl
  | call machine =>
    simp [Code.compileAt,avoidsCode,List.all_map,Function.comp_def,avoids_relocate]
  | seq a b ha hb => simp [Code.compileAt,avoidsCode,ha,hb]
  | branch r a b ha hb => simp [Code.compileAt,avoidsCode,avoids,ha,hb]
  | loop r a ha => simp [Code.compileAt,avoidsCode,avoids,ha]

theorem compile_avoids (archive : ℕ) (body : Code) :
    body.compile.code.all (avoids archive)=avoidsCode archive body := by
  simp [Code.compile,compileAt_avoids,avoids]

end Maxwell.Continuum.OutputCapture
