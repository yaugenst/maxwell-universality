import Maxwell.Cost.OutputCapture.Code
import Maxwell.Cost.Structured.Footprint

/-! Syntactic non-access, including reads, of the retained output tape. -/
namespace Maxwell.Cost.OutputCapture
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

theorem avoidsCode_protectsTape (archive : ℕ) (body : Code)
    (h : avoidsCode archive body=true) : body.protectsTape archive=true := by
  induction body with
  | skip => rfl
  | call machine =>
    apply List.all_eq_true.mpr
    intro instruction hi
    have hn := List.all_eq_true.mp h instruction hi
    cases instruction <;> simp_all [avoids,BitRAMInstruction.protectsTape]
  | seq a b ha hb =>
    simp only [avoidsCode,Bool.and_eq_true] at h
    simp only [Code.protectsTape,ha h.1,hb h.2,Bool.and_self]
  | branch r a b ha hb =>
    simp only [avoidsCode,Bool.and_eq_true] at h
    simp only [Code.protectsTape,ha h.1,hb h.2,Bool.and_self]
  | loop r a ha => exact ha h


end Maxwell.Cost.OutputCapture
